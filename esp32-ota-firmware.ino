/*
 * ESP32-S3-N16R8  --  Hardened Internet OTA "seed" sketch
 * ============================================================================
 * arduino-esp32 core 3.3.10  (ESP32 Arduino 3.x API)
 *
 * WHAT IT DOES
 *   - Joins 2.4GHz WiFi (credentials stored on-device in NVS, NOT compiled in),
 *     non-blocking, with an explicit reconnect state.
 *   - Continuously animates the onboard WS2812 RGB on GPIO48 via the builtin
 *     neopixelWrite() so you can SEE the device is alive. The base color is a
 *     function of FIRMWARE_VERSION, so a successful internet OTA visibly CHANGES
 *     the color after the device self-reboots into the new image.
 *   - Every ~30s checks https://.../version.txt and, ONLY if the remote integer
 *     is STRICTLY GREATER than FIRMWARE_VERSION, downloads+flashes firmware.bin
 *     via httpUpdate (which reboots on success). White flashing during update.
 *
 * ============================================================================
 *  WHY WIFI CREDS ARE NOT IN THE BINARY
 * ============================================================================
 *  The published firmware.bin lives in a PUBLIC repo. Compiling WiFi creds in
 *  would leak the password to the world. Instead creds are stored in NVS (flash
 *  key-value store) and provisioned ONCE over USB serial. NVS lives in its own
 *  partition, so it SURVIVES reboots AND OTA updates -- provision once per board.
 *
 *  PROVISIONING (send over serial, newline-terminated):
 *     SETWIFI <ssid> <password>     e.g.  SETWIFI MyNetwork MyPassword
 *        (ssid = first token; password = the rest, so passwords may contain
 *         spaces; the ssid may not.)
 *     CLEARWIFI                     erase stored creds, re-enter provisioning
 *     SHOWWIFI                      print stored ssid (password masked)
 *
 * ============================================================================
 *  #1 PRIORITY: SAFE AGAINST RE-FLASH BOOT LOOPS
 * ============================================================================
 *  (A) RUNTIME GUARD: we update ONLY when (remote > FIRMWARE_VERSION), strictly.
 *      Equal/lesser/unparseable/fetch-failure NEVER triggers a flash. A fetch or
 *      parse failure is treated as "no update" and NEVER as version 0 (which
 *      would force an endless downgrade-reflash).
 *
 *  (B) TRUNCATION GUARD (the weak -76 dBm link can deliver partial bodies):
 *      we capture Content-Length via https.getSize() and REQUIRE the received
 *      body length to match it before trusting the number. A truncated
 *      "10" -> "1" still passes an all-digits check, so without this guard the
 *      device could silently mis-read the version. Mismatch => "no update".
 *
 *  (C) *** BINDING RELEASE INVARIANT (cannot be enforced in firmware) ***
 *      The FIRMWARE_VERSION compiled into firmware.bin MUST EQUAL the integer
 *      published in version.txt for that SAME release. If firmware.bin ships
 *      with a FIRMWARE_VERSION <= the number in version.txt, the new image also
 *      sees remote > local and re-flashes FOREVER. Bump BOTH together.
 *
 *  (D) FAILURE BACKOFF: after a failed download we reset the check timer, skip
 *      re-downloading that exact failed version, and grow the interval to a cap.
 *
 * Build/publish notes are at the bottom of this file.
 * ============================================================================
 */

#include <WiFi.h>
#include <WiFiClientSecure.h>
#include <HTTPClient.h>
#include <HTTPUpdate.h>
#include <Preferences.h>

// ===================== COMPILE-TIME CONFIG =====================
// *** BUMP THIS for each published build, and set version.txt to the SAME int. ***
#define FIRMWARE_VERSION 3

// WiFi credentials live in NVS (see provisioning notes in the header). They are
// loaded into these at boot; never hard-coded.
static Preferences prefs;
static const char* NVS_NAMESPACE = "wifi";
static String g_ssid = "";
static String g_pass = "";
static bool   haveCreds = false;

static const char* VERSION_URL  =
  "https://raw.githubusercontent.com/mridulgupta369/esp32-ota-firmware/main/version.txt";
static const char* FIRMWARE_URL =
  "https://raw.githubusercontent.com/mridulgupta369/esp32-ota-firmware/main/firmware.bin";

// Onboard addressable RGB LED (WS2812) data pin. GPIO48 is the legit onboard
// LED and is NOT a forbidden pin (forbidden: 26-37, 19/20, 43/44).
static const int RGB_PIN = 48;

// Timing (all millis()-based; nothing blocks the blink except the actual fetch/download)
static const uint32_t OTA_CHECK_INTERVAL_MS   = 30000;   // ~30s between OTA checks
static const uint32_t OTA_CHECK_BACKOFF_MAX_MS = 300000; // cap backoff at 5 min
static const uint32_t BLINK_INTERVAL_MS       = 250;     // LED animation step
static const uint32_t WIFI_CONNECT_TIMEOUT_MS = 20000;   // per-attempt connect window
static const uint32_t WIFI_RETRY_BACKOFF_MS   = 5000;    // wait between reconnect attempts
static const int      HTTP_CONNECT_TIMEOUT_MS = 8000;    // TLS connect bound (ms, real)
static const int      HTTP_READ_TIMEOUT_MS    = 8000;    // socket read bound (ms, real)
static const int      TLS_TIMEOUT_S           = 12;      // WiFiClientSecure timeout (SECONDS)
static const uint32_t UPDATE_FLASH_MIN_MS     = 70;      // throttle white strobe during DL

// Defensive parse bounds for version.txt
static const int VERSION_MIN          = 1;       // FW starts at 1; reject 0/sentinels
static const int VERSION_MAX          = 1000000; // sane upper bound
static const int MAX_VERSION_BYTES    = 16;      // reject absurdly long bodies

// ===================== STATE MACHINE =====================
enum AppState {
  ST_NEEDS_PROV,        // no WiFi creds stored; waiting for SETWIFI over serial
  ST_WIFI_CONNECTING,   // trying to (re)join WiFi
  ST_ONLINE,            // connected, animating + periodic OTA checks
  ST_UPDATING           // OTA download/flash in progress (brief, blocking)
};
static AppState state = ST_NEEDS_PROV;

// ===================== TIMERS / FLAGS =====================
static uint32_t lastBlinkMs        = 0;
static uint32_t lastOtaCheckMs     = 0;
static uint32_t otaCheckIntervalMs = OTA_CHECK_INTERVAL_MS; // grows on failure
static uint32_t wifiAttemptStartMs = 0;
static uint32_t lastWifiRetryMs    = 0;
static bool     blinkPhase         = false;
static bool     wifiStarted        = false;
static int      lastFailedRemote   = -1;   // remote version that failed to flash; skip it

// ============================================================
//  LED HELPERS  (neopixelWrite is the core builtin; 0-255 values)
// ============================================================

// Map FIRMWARE_VERSION -> a distinct base color so an OTA visibly changes color.
static void versionColor(uint8_t& r, uint8_t& g, uint8_t& b) {
  switch (FIRMWARE_VERSION % 6) {
    case 1:  r = 0;   g = 0;   b = 255; break;  // blue
    case 2:  r = 0;   g = 255; b = 0;   break;  // green
    case 3:  r = 255; g = 0;   b = 0;   break;  // red
    case 4:  r = 255; g = 0;   b = 255; break;  // magenta
    case 5:  r = 0;   g = 255; b = 255; break;  // cyan
    default: r = 255; g = 255; b = 0;   break;  // yellow (case 0 => v6,12,...)
  }
}

static inline void ledOff() { neopixelWrite(RGB_PIN, 0, 0, 0); }

// Online "alive" pulse in the version color.
static void ledOnlineStep() {
  if (blinkPhase) {
    uint8_t r, g, b;
    versionColor(r, g, b);
    neopixelWrite(RGB_PIN, r, g, b);
  } else {
    ledOff();
  }
}

// WiFi-searching indicator: dim amber blink (distinct from any version color).
static void ledWifiStep() {
  if (blinkPhase) neopixelWrite(RGB_PIN, 40, 20, 0);
  else            ledOff();
}

// Needs-provisioning indicator: purple blink (distinct from amber & version colors).
static void ledProvStep() {
  if (blinkPhase) neopixelWrite(RGB_PIN, 64, 0, 64);
  else            ledOff();
}

// Fast white flash, millis()-throttled. Driven from httpUpdate's onProgress hook
// so the LED keeps flashing DURING the blocking download.
static void ledUpdateFlash() {
  static uint32_t lastFlash = 0;
  static bool     on        = false;
  uint32_t now = millis();
  if (now - lastFlash < UPDATE_FLASH_MIN_MS) return;
  lastFlash = now;
  on = !on;
  if (on) neopixelWrite(RGB_PIN, 255, 255, 255);
  else    ledOff();
}

// ============================================================
//  CREDENTIALS (NVS) + SERIAL PROVISIONING
// ============================================================
static void loadCreds() {
  prefs.begin(NVS_NAMESPACE, true);      // read-only
  g_ssid = prefs.getString("ssid", "");
  g_pass = prefs.getString("pass", "");
  prefs.end();
  haveCreds = (g_ssid.length() > 0);
}

static void saveCreds(const String& ssid, const String& pass) {
  prefs.begin(NVS_NAMESPACE, false);     // read-write
  prefs.putString("ssid", ssid);
  prefs.putString("pass", pass);
  prefs.end();
  g_ssid = ssid;
  g_pass = pass;
  haveCreds = (g_ssid.length() > 0);
}

static void clearCreds() {
  prefs.begin(NVS_NAMESPACE, false);
  prefs.clear();
  prefs.end();
  g_ssid = "";
  g_pass = "";
  haveCreds = false;
}

static void printProvPrompt() {
  Serial.println("[PROV] No WiFi credentials stored on this device.");
  Serial.println("[PROV] Send over serial:  SETWIFI <ssid> <password>");
  Serial.println("[PROV]   example:          SETWIFI MyNetwork MyPassword");
}

// Read available serial bytes; act on provisioning commands.
// Returns true if credentials were just SET (caller should start connecting).
static bool handleSerialProvisioning() {
  static String line = "";
  bool credsSet = false;
  while (Serial.available() > 0) {
    char c = (char)Serial.read();
    if (c == '\r') continue;
    if (c == '\n') {
      line.trim();
      if (line.startsWith("SETWIFI ")) {
        String rest = line.substring(8);
        rest.trim();
        int sp = rest.indexOf(' ');
        if (sp > 0) {
          String ssid = rest.substring(0, sp);
          String pass = rest.substring(sp + 1);
          ssid.trim();
          saveCreds(ssid, pass);
          Serial.printf("[PROV] Saved SSID \"%s\" (password %u chars). Connecting...\n",
                        ssid.c_str(), (unsigned)pass.length());
          credsSet = true;
        } else {
          Serial.println("[PROV] Bad format. Use: SETWIFI <ssid> <password>");
        }
      } else if (line == "CLEARWIFI") {
        clearCreds();
        Serial.println("[PROV] Credentials cleared. Send SETWIFI <ssid> <password>.");
      } else if (line == "SHOWWIFI") {
        Serial.printf("[PROV] Stored SSID: \"%s\"  password: %s\n",
                      g_ssid.c_str(), haveCreds ? "(set)" : "(none)");
      } else if (line.length() > 0) {
        Serial.printf("[PROV] Unknown command: \"%s\"\n", line.c_str());
      }
      line = "";
    } else if (line.length() < 200) {
      line += c;
    }
  }
  return credsSet;
}

// ============================================================
//  WIFI
// ============================================================
static void wifiBeginAttempt() {
  Serial.printf("[WiFi] Connecting to SSID \"%s\" ...\n", g_ssid.c_str());
  if (!wifiStarted) {
    // One-time stack setup; avoid re-tearing-down the radio on every retry
    // (repeated disconnect() can abort an in-progress association on a weak link).
    WiFi.persistent(false);
    WiFi.mode(WIFI_STA);
    WiFi.setSleep(false);            // steadier RSSI on a weak (-76 dBm) link
    WiFi.setAutoReconnect(true);
    wifiStarted = true;
  }
  WiFi.begin(g_ssid.c_str(), g_pass.c_str());  // single begin() per attempt window
  wifiAttemptStartMs = millis();
  lastWifiRetryMs    = millis();
}

// ============================================================
//  VERSION FETCH + DEFENSIVE PARSE  (with Content-Length truncation guard)
//  Returns true only if a COMPLETE, valid integer was parsed -> *out.
//  ANY failure returns false (caller treats as "no update"; never as 0).
// ============================================================
static bool fetchRemoteVersion(int& out) {
  if (WiFi.status() != WL_CONNECTED) {
    Serial.println("[VER] Skipped: WiFi not connected.");
    return false;
  }

  // Stack-scoped TLS client so its ~40KB+ buffers are freed promptly on return.
  WiFiClientSecure client;
  client.setInsecure();                 // hobby project: skip cert validation
  client.setTimeout(TLS_TIMEOUT_S);     // WiFiClient base: SECONDS (best-effort)

  HTTPClient https;
  https.setConnectTimeout(HTTP_CONNECT_TIMEOUT_MS); // ms; the REAL connect guard
  https.setTimeout(HTTP_READ_TIMEOUT_MS);           // ms; the REAL read guard
  https.setReuse(false);
  https.setFollowRedirects(HTTPC_STRICT_FOLLOW_REDIRECTS); // Fastly/GitHub may 302

  // Cache-buster: raw.githubusercontent.com (Fastly) caches by full URL incl.
  // query string. A unique ?t= each fetch bypasses any stale 200/404 cache, so
  // we always see the latest version.txt the instant it's pushed.
  String vurl = String(VERSION_URL) + "?t=" + String(millis());
  if (!https.begin(client, vurl)) {
    Serial.println("[VER] https.begin() failed -> no update.");
    return false;
  }

  int code = https.GET();
  if (code != HTTP_CODE_OK) {           // 200 only; redirects/errors -> no update
    Serial.printf("[VER] HTTP GET failed, code=%d (%s) -> no update.\n",
                  code, https.errorToString(code).c_str());
    https.end();
    return false;
  }

  // Content-Length BEFORE buffering. Reject negative (unknown/chunked) or absurd.
  int len = https.getSize();
  if (len < 0 || len > MAX_VERSION_BYTES) {
    Serial.printf("[VER] Content-Length %d invalid/too large -> no update.\n", len);
    https.end();
    return false;
  }

  String body = https.getString();
  https.end();   // close before parsing; client frees on scope exit

  // --- TRUNCATION GUARD: received bytes must equal the declared length -------
  // (Weak link can deliver a partial body; a truncated all-digit number would
  //  silently corrupt the version compare. Require an exact length match.)
  if ((int)body.length() != len) {
    Serial.printf("[VER] Truncated body: got %u, expected %d -> no update.\n",
                  (unsigned)body.length(), len);
    return false;
  }

  // --- Defensive parse --------------------------------------------------------
  body.trim();                          // strip whitespace/CR/LF (trailing newline ok)
  if (body.length() == 0) {
    Serial.println("[VER] Empty body after trim -> no update.");
    return false;
  }
  if (body.length() > (unsigned)MAX_VERSION_BYTES) {
    Serial.println("[VER] Over-long version string -> no update.");
    return false;
  }
  for (unsigned int i = 0; i < body.length(); i++) {
    if (!isDigit((unsigned char)body.charAt(i))) {   // cast: safe for high bytes
      Serial.printf("[VER] Non-numeric char 0x%02X -> no update.\n",
                    (unsigned char)body.charAt(i));
      return false;
    }
  }

  long val = body.toInt();              // safe now: confirmed all-digits
  if (val < VERSION_MIN || val > VERSION_MAX) {
    Serial.printf("[VER] Parsed %ld out of range [%d..%d] -> no update.\n",
                  val, VERSION_MIN, VERSION_MAX);
    return false;
  }

  out = (int)val;
  Serial.printf("[VER] Remote version parsed OK: %d (local FW=%d)\n",
                out, FIRMWARE_VERSION);
  return true;
}

// ============================================================
//  OTA APPLY  (only ever called after a STRICT remote>local check)
//  Returns true if a flash was applied (won't return: device reboots),
//  false on NO_UPDATES/FAILED so the caller can apply backoff.
// ============================================================
static bool performOtaUpdate(int remote) {
  Serial.printf("[OTA] Newer firmware confirmed (remote %d > local %d). Downloading...\n",
                remote, FIRMWARE_VERSION);
  state = ST_UPDATING;

  // Visible "updating" state immediately, before the (blocking) handshake, in
  // case onProgress never fires due to a stalled connect.
  neopixelWrite(RGB_PIN, 255, 255, 255);

  // Fresh stack-scoped TLS client for the larger, blocking binary transfer.
  WiFiClientSecure client;
  client.setInsecure();
  client.setTimeout(TLS_TIMEOUT_S);

  httpUpdate.rebootOnUpdate(true);                          // default; explicit
  httpUpdate.setFollowRedirects(HTTPC_STRICT_FOLLOW_REDIRECTS); // CDN may 302

  // Animate the WS2812 white-flash DURING the blocking transfer (throttled).
  httpUpdate.onStart([]() { Serial.println("[OTA] httpUpdate start."); });
  httpUpdate.onProgress([](int cur, int total) {           // sig: void(int,int)
    ledUpdateFlash();
    if (total > 0) {
      static int lastPct = -1;
      int pct = (int)((int64_t)cur * 100 / total);
      if (pct != lastPct && (pct % 10 == 0)) {
        Serial.printf("[OTA] %d%% (%d/%d)\n", pct, cur, total);
        lastPct = pct;
      }
    }
  });
  httpUpdate.onError([](int err) { Serial.printf("[OTA] onError code=%d\n", err); });

  // Cache-buster (same reason as the version fetch): always pull the freshly
  // published binary, never a stale CDN copy -- avoids flashing an old image.
  String furl = String(FIRMWARE_URL) + "?t=" + String(millis());
  t_httpUpdate_return ret = httpUpdate.update(client, furl);

  switch (ret) {
    case HTTP_UPDATE_OK:
      Serial.println("[OTA] HTTP_UPDATE_OK (rebooting).");   // normally unreachable
      return true;

    case HTTP_UPDATE_NO_UPDATES:
      Serial.println("[OTA] HTTP_UPDATE_NO_UPDATES (server had nothing new).");
      return false;

    case HTTP_UPDATE_FAILED:
    default:
      Serial.printf("[OTA] HTTP_UPDATE_FAILED err=%d: %s\n",
                    httpUpdate.getLastError(),
                    httpUpdate.getLastErrorString().c_str());
      return false;
  }
}

// ============================================================
//  SETUP
// ============================================================
void setup() {
  Serial.begin(115200);
  delay(300);   // let USB CDC settle; do NOT block waiting for a host reader.

  // Show version color briefly at boot as a sanity marker.
  uint8_t r, g, b; versionColor(r, g, b);
  neopixelWrite(RGB_PIN, r, g, b);

  Serial.println();
  Serial.println("==============================================");
  Serial.printf ("  ESP32-S3 OTA Seed  |  FIRMWARE_VERSION = %d\n", FIRMWARE_VERSION);
  Serial.printf ("  Converged when version.txt == %d\n", FIRMWARE_VERSION);
  Serial.println("==============================================");

  loadCreds();
  if (haveCreds) {
    Serial.printf("[PROV] Loaded stored SSID \"%s\" from NVS.\n", g_ssid.c_str());
    wifiBeginAttempt();
    state = ST_WIFI_CONNECTING;
  } else {
    printProvPrompt();
    state = ST_NEEDS_PROV;
  }

  lastBlinkMs    = millis();
  lastOtaCheckMs = millis();   // first OTA check ~one full interval after boot
}

// ============================================================
//  LOOP  (state machine; fully non-blocking except the OTA fetch/download)
// ============================================================
void loop() {
  uint32_t now = millis();

  // ---- 0. Always accept provisioning commands over serial (re-provision anytime) ----
  if (handleSerialProvisioning()) {
    wifiStarted = false;          // force fresh WiFi.mode setup with the new creds
    wifiBeginAttempt();
    state = ST_WIFI_CONNECTING;
  }
  if (!haveCreds && state != ST_NEEDS_PROV) {
    state = ST_NEEDS_PROV;        // e.g. after CLEARWIFI
  }

  // ---- 1. LED animation (always runs, every BLINK_INTERVAL_MS) ----
  if (now - lastBlinkMs >= BLINK_INTERVAL_MS) {
    lastBlinkMs = now;
    blinkPhase  = !blinkPhase;
    switch (state) {
      case ST_NEEDS_PROV:      ledProvStep();   break;
      case ST_WIFI_CONNECTING: ledWifiStep();   break;
      case ST_ONLINE:          ledOnlineStep(); break;
      case ST_UPDATING:        /* LED driven by onProgress hook */ break;
    }
  }

  // ---- 2. State machine ----
  switch (state) {

    case ST_NEEDS_PROV: {
      // Waiting for SETWIFI over serial (handled at top of loop). Reprint the
      // prompt occasionally so a freshly-attached monitor sees what to do.
      static uint32_t lastPrompt = 0;
      if (now - lastPrompt >= 5000) { lastPrompt = now; printProvPrompt(); }
      break;
    }

    case ST_WIFI_CONNECTING: {
      wl_status_t ws = WiFi.status();
      if (ws == WL_CONNECTED) {
        Serial.printf("[WiFi] Connected. IP=%s RSSI=%d dBm\n",
                      WiFi.localIP().toString().c_str(), WiFi.RSSI());
        state          = ST_ONLINE;
        lastOtaCheckMs = now;            // settle before first check
      } else if (now - wifiAttemptStartMs >= WIFI_CONNECT_TIMEOUT_MS) {
        if (now - lastWifiRetryMs >= WIFI_RETRY_BACKOFF_MS) {
          Serial.println("[WiFi] Connect timeout; retrying begin()...");
          wifiBeginAttempt();            // single begin(); no radio teardown
        }
      }
      break;
    }

    case ST_ONLINE: {
      if (WiFi.status() != WL_CONNECTED) {
        Serial.println("[WiFi] Link lost; reconnecting...");
        wifiBeginAttempt();
        state = ST_WIFI_CONNECTING;
        break;
      }

      if (now - lastOtaCheckMs >= otaCheckIntervalMs) {
        lastOtaCheckMs = now;            // measure interval from CHECK START
        Serial.printf("[OTA] Periodic check. Local FW=%d\n", FIRMWARE_VERSION);

        int remote = -1;
        if (fetchRemoteVersion(remote)) {
          if (remote <= FIRMWARE_VERSION) {
            Serial.printf("[OTA] Remote %d <= local %d -> no update.\n",
                          remote, FIRMWARE_VERSION);
            otaCheckIntervalMs = OTA_CHECK_INTERVAL_MS;     // healthy; reset backoff
          } else if (remote == lastFailedRemote) {
            // We already tried this exact remote version and it failed to flash.
            // Don't re-download it every cycle (avoids retry storm on a weak link).
            Serial.printf("[OTA] Remote %d already failed; skipping (backoff).\n", remote);
          } else {
            // --- THE critical gate: strictly greater AND not a known-bad version ---
            bool flashed = performOtaUpdate(remote);  // blocks; reboots on success
            if (!flashed) {
              lastFailedRemote = remote;              // remember & skip next time
              otaCheckIntervalMs = (otaCheckIntervalMs < OTA_CHECK_BACKOFF_MAX_MS)
                                     ? (otaCheckIntervalMs * 2) : OTA_CHECK_BACKOFF_MAX_MS;
              if (otaCheckIntervalMs > OTA_CHECK_BACKOFF_MAX_MS)
                otaCheckIntervalMs = OTA_CHECK_BACKOFF_MAX_MS;
              Serial.printf("[OTA] Update failed; next check in %lu ms.\n",
                            (unsigned long)otaCheckIntervalMs);
            }
            state = ST_ONLINE;
            lastOtaCheckMs = millis();   // don't let the blocking DL eat the interval
          }
        } else {
          // Fetch/parse/truncation failure: strictly "no update". Never version 0.
          Serial.println("[OTA] Version fetch/parse failed -> no update this cycle.");
        }
      }
      break;
    }

    case ST_UPDATING:
      // performOtaUpdate() runs synchronously and resets state itself.
      break;
  }

  // ---- 3. Cooperative yield: keep FreeRTOS IDLE / WiFi stack healthy ----
  // (loopTask is not WDT-subscribed by default in core 3.x, so the multi-second
  //  blocking download won't WDT-panic; this yield is for RTOS task health.)
  delay(2);
}

/* ============================================================================
 * PUBLISHING A NEW VERSION (must keep the two numbers EQUAL -- invariant C):
 *   1. Edit this file: set #define FIRMWARE_VERSION to the new int (e.g. 2).
 *   2. Compile to firmware.bin with the FULL OTA FQBN (note FlashSize=16M is
 *      REQUIRED on the N16R8 or the 16MB partition table is rejected at boot):
 *        esp32:esp32:esp32s3:USBMode=hwcdc,CDCOnBoot=cdc,
 *          PartitionScheme=app3M_fat9M_16MB,FlashSize=16M
 *   3. Put the SAME int (e.g. "2") into version.txt.
 *   4. Commit firmware.bin + version.txt together; push to main.
 *   Devices running FW=1 will see remote(2) > local(1), flash, reboot, and show
 *   the v2 color (green). The new image has local=2 == remote=2 -> converged.
 *   WiFi creds are in NVS and survive the OTA, so no re-provisioning is needed.
 * ========================================================================== */
