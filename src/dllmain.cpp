#include <windows.h>
#include <psapi.h>
#include <intrin.h>
#include <cstdio>
#include <cstring>
#include <string>

// ============================================================
//  Private Storage Anywhere v1.2.0
//
//  Opens the Camp Warehouse (Private Storage) from anywhere
//  with a hotkey (default F6) or controller button.
// ============================================================

static uintptr_t g_gameBase = 0, g_imageSize = 0;
static bool g_ready = false;
static FILE* g_logFile = nullptr;
static HMODULE g_hModule = nullptr;
static HWND g_gameWindow = nullptr;
static WNDPROC g_originalWndProc = nullptr;
static bool g_enabled = true, g_debugLog = true;
static DWORD g_hotkey = VK_F6;
static DWORD g_modifierKey = 0;
static DWORD g_reloadKey = 0;
static char g_iniPath[MAX_PATH] = {};

// Resolved function addresses
static uintptr_t g_fnHandler = 0;
static uintptr_t g_fnModeSwitcher = 0, g_fnCanShow = 0, g_fnSetInventory = 0;
static uintptr_t g_fnSetTitle = 0;
static uintptr_t g_fnSetCursorVisible = 0;  // thunk_FUN_1524be5a0(cursorObj, show, force)
static uintptr_t g_warehouseVtableEntry = 0;  // vtable address containing handler — used for auto-capture verification
static uintptr_t g_warehouseVtableStart = 0;  // vtable start of warehouse class — set on first successful capture

// Captured game state (accessed from multiple threads via Interlocked ops)
static volatile LONG64 g_mainChar = 0;
static volatile LONG64 g_handlerThis = 0;
static volatile LONG64 g_cursorObj = 0;
static volatile LONG g_warehouseActive = 0;
static volatile LONG g_handlerHitCount = 0;
static volatile LONG g_canShowSeen118 = 0;  // set to 1 once +0x118 has been seen as 1

// Constants
static volatile LONG g_warehousePanelId = 0x0059;  // default, verified dynamically at runtime
static const char* WAREHOUSE_INIT_STRING = "Character,Focus,True;CampWareHouse,Focus,True";

// Saved mode bytes for restore on close
static uint8_t g_savedModes[7] = {};
static uint8_t g_savedSubtypes[15] = {};
static bool g_cursorShownByMod = false;
static volatile LONG g_modeByteLock = 0;  // Spinlock for mode byte read/write
static volatile LONG g_modeSwitchByMod = 0;  // 1 when WE call fnMode, 0 otherwise
static volatile ULONGLONG g_openTimestamp = 0;  // GetTickCount64 at warehouse open (grace period)

// Delayed bridge+8 check state
static volatile LONG64 g_delayCheckChild = 0;   // child of parent+0x060
static volatile LONG64 g_delayCheckNode060 = 0;  // parent+0x060 node itself

// Forward declaration (defined later in Utilities section)
static void Log(const char* fmt, ...);

static DWORD WINAPI DelayedBridgeCheck(LPVOID /*param*/) {
    DWORD delays[] = { 200, 300, 500, 1000, 2000 };
    for (int i = 0; i < 5; i++) {
        Sleep(delays[i]);
        if (!InterlockedCompareExchange(&g_warehouseActive, 0, 0)) {
            Log("  DELAY[%dms]: warehouse closed, aborting", delays[i]);
            break;
        }
        uintptr_t child = (uintptr_t)InterlockedCompareExchange64(&g_delayCheckChild, 0, 0);
        uintptr_t node060 = (uintptr_t)InterlockedCompareExchange64(&g_delayCheckNode060, 0, 0);
        if (!child || !node060) break;
        __try {
            uintptr_t na8 = *(uintptr_t*)(node060 + 0xa8);
            uintptr_t nb8 = 0;
            if (na8 > 0x10000 && na8 < 0x7FFFFFFFFFFF)
                nb8 = *(uintptr_t*)(na8 + 8);
            uintptr_t ca8 = *(uintptr_t*)(child + 0xa8);
            uintptr_t cb8 = 0;
            if (ca8 > 0x10000 && ca8 < 0x7FFFFFFFFFFF)
                cb8 = *(uintptr_t*)(ca8 + 8);
            int32_t c38 = *(int32_t*)(child + 0x38);
            uintptr_t cp30 = *(uintptr_t*)(child + 0x30);
            uintptr_t gc0b8 = 0, gc1b8 = 0;
            if (c38 >= 1 && cp30 > 0x10000 && cp30 < 0x7FFFFFFFFFFF) {
                uintptr_t gc0 = *(uintptr_t*)cp30;
                if (gc0 > 0x10000 && gc0 < 0x7FFFFFFFFFFF) {
                    uintptr_t ga8 = *(uintptr_t*)(gc0 + 0xa8);
                    if (ga8 > 0x10000 && ga8 < 0x7FFFFFFFFFFF)
                        gc0b8 = *(uintptr_t*)(ga8 + 8);
                }
                if (c38 >= 2) {
                    uintptr_t gc1 = *(uintptr_t*)(cp30 + 8);
                    if (gc1 > 0x10000 && gc1 < 0x7FFFFFFFFFFF) {
                        uintptr_t ga8 = *(uintptr_t*)(gc1 + 0xa8);
                        if (ga8 > 0x10000 && ga8 < 0x7FFFFFFFFFFF)
                            gc1b8 = *(uintptr_t*)(ga8 + 8);
                    }
                }
            }
            Log("  DELAY[%dms]: node.b8=%p child.b8=%p gc0.b8=%p gc1.b8=%p",
                delays[i], (void*)nb8, (void*)cb8, (void*)gc0b8, (void*)gc1b8);
            if (nb8 || cb8 || gc0b8 || gc1b8)
                Log("  DELAY[%dms]: *** BRIDGE+8 APPEARED! ***", delays[i]);
        } __except(EXCEPTION_EXECUTE_HANDLER) {
            Log("  DELAY[%dms]: EXCEPTION", delays[i]);
            break;
        }
    }
    return 0;
}

// Hook cleanup: saved original bytes for safe DLL unload
static uint8_t g_origHandlerBytes[15] = {};
static uint8_t g_origModeSwitcherBytes[15] = {};
static uint8_t g_origCanShowBytes[14] = {};
static uintptr_t g_hookAddrHandler = 0, g_hookAddrModeSwitcher = 0, g_hookAddrCanShow = 0;



#define WM_TRIGGER_WAREHOUSE (WM_USER + 602)

// ============================================================
//  Raw Input — DualSense / DualShock button detection
//  The game uses WM_INPUT (Raw Input + HID) for controller input.
//  We intercept WM_INPUT in the already-hooked WndProc to detect
//  buttons on Sony controllers (works for DirectInput/HID).
// ============================================================

// Sony Vendor ID
#define SONY_VID 0x054C
// Known Sony controller PIDs
#define DS4_PID_1   0x05C4  // DualShock 4 v1
#define DS4_PID_2   0x09CC  // DualShock 4 v2
#define DS5_PID     0x0CE6  // DualSense
#define DS5_EDGE    0x0DF2  // DualSense Edge

// Circle button bit (always active for close-on-release)
#define CIRCLE_BIT  0x40    // bit 6 in buttons1 (byte offset 0)

// Configurable PSButton — byte offset relative to buttons1, and bit mask
// Set by LoadConfig from INI "PSButton" string
static int  g_psButtonByteOff = 1;   // default: buttons2 (offset +1 from buttons1)
static BYTE g_psButtonBitMask = 0x10; // default: Share = bit 4
static bool g_psButtonEnabled = true; // false if PSButton=none

static bool g_circleWasDown   = false;
static bool g_psButtonWasDown = false;

// Cached device identification (so we only call GetRawInputDeviceInfo once per handle)
static HANDLE g_cachedHidDevice = nullptr;
static bool   g_cachedIsSony = false;
static int    g_cachedReportOffset = -1;  // offset to buttons1 byte (-1 = unknown)

// Parsed button state from last WM_INPUT
static bool g_lastCircle   = false;
static bool g_lastPSButton = false;

static void IdentifyHidDevice(HANDLE hDevice) {
    if (hDevice == g_cachedHidDevice) return;
    g_cachedHidDevice = hDevice;
    g_cachedIsSony = false;
    g_cachedReportOffset = -1;

    RID_DEVICE_INFO info = {};
    info.cbSize = sizeof(RID_DEVICE_INFO);
    UINT sz = sizeof(info);
    if (GetRawInputDeviceInfoA(hDevice, RIDI_DEVICEINFO, &info, &sz) == (UINT)-1) return;
    if (info.dwType != RIM_TYPEHID) return;
    if (info.hid.dwVendorId != SONY_VID) return;

    g_cachedIsSony = true;
    WORD pid = (WORD)info.hid.dwProductId;
    // DualShock 4: buttons1 at report byte 5 (USB) / byte 5 (BT w/ report ID stripped)
    // DualSense:   buttons1 at report byte 8 (USB report 0x01) / byte 9 (BT report 0x31)
    // Note: Raw Input strips the report ID for USB, keeps it for BT
    if (pid == DS4_PID_1 || pid == DS4_PID_2) {
        g_cachedReportOffset = 5;  // DualShock 4 USB
    } else if (pid == DS5_PID || pid == DS5_EDGE) {
        g_cachedReportOffset = 8;  // DualSense USB
    }
    Log("HID device identified: VID=%04X PID=%04X → buttons1 offset=%d",
        SONY_VID, pid, g_cachedReportOffset);
}

// Parses Circle + configured PSButton state from WM_INPUT HID report.
// Stores results in g_lastCircle and g_lastPSButton.
static void ParseSonyButtons(LPARAM lParam) {
    g_lastCircle = false;
    g_lastPSButton = false;

    UINT dwSize = 0;
    GetRawInputData((HRAWINPUT)lParam, RID_INPUT, nullptr, &dwSize, sizeof(RAWINPUTHEADER));
    if (dwSize == 0 || dwSize > 1024) return;

    BYTE buf[1024];
    if (GetRawInputData((HRAWINPUT)lParam, RID_INPUT, buf, &dwSize, sizeof(RAWINPUTHEADER)) == (UINT)-1)
        return;

    RAWINPUT* raw = (RAWINPUT*)buf;
    if (raw->header.dwType != RIM_TYPEHID) return;
    if (raw->data.hid.dwCount == 0 || raw->data.hid.dwSizeHid == 0) return;

    IdentifyHidDevice(raw->header.hDevice);
    if (!g_cachedIsSony || g_cachedReportOffset < 0) return;

    BYTE* report = raw->data.hid.bRawData;
    DWORD reportLen = raw->data.hid.dwSizeHid;

    // Handle Bluetooth reports with report ID prefix
    int offset = g_cachedReportOffset;
    if (reportLen > 40 && report[0] == 0x31) {
        // DualSense Bluetooth: report ID 0x31, data shifted by +1
        offset = 9;
    } else if (reportLen > 40 && report[0] == 0x11) {
        // DualShock 4 Bluetooth: report ID 0x11, buttons at offset 7
        offset = 7;
    }

    if ((DWORD)offset >= reportLen) return;

    // Circle is always at buttons1 (offset + 0)
    g_lastCircle = (report[offset] & CIRCLE_BIT) != 0;

    // PSButton uses configurable byte offset from buttons1
    if (g_psButtonEnabled) {
        int psOff = offset + g_psButtonByteOff;
        if ((DWORD)psOff < reportLen) {
            g_lastPSButton = (report[psOff] & g_psButtonBitMask) != 0;
        }
    }
}

// ============================================================
//  XInput (dynamic loading)
// ============================================================
struct XINPUT_GAMEPAD_LOCAL {
    WORD  wButtons;
    BYTE  bLeftTrigger;
    BYTE  bRightTrigger;
    SHORT sThumbLX, sThumbLY;
    SHORT sThumbRX, sThumbRY;
};
struct XINPUT_STATE_LOCAL {
    DWORD dwPacketNumber;
    XINPUT_GAMEPAD_LOCAL Gamepad;
};
typedef DWORD (WINAPI *PFN_XInputGetState)(DWORD, XINPUT_STATE_LOCAL*);
static PFN_XInputGetState g_pXInputGetState = nullptr;
static HMODULE g_hXInput = nullptr;
static WORD g_controllerButton = 0;
static WORD g_controllerModifier = 0;
static WORD g_prevButtons = 0;

// ============================================================
//  Utilities
// ============================================================
static void Log(const char* fmt, ...) {
    if (!g_logFile) return;
    va_list a; va_start(a, fmt);
    vfprintf(g_logFile, fmt, a); fprintf(g_logFile, "\n"); fflush(g_logFile);
    va_end(a);
}

// ============================================================
//  Localization — read game language and return translated title
//  Language byte at gameBase+0x599772D (DAT_14599772d)
//  Set by FUN_1404864a0 from Steam API language detection.
//  SetTitle's internal char→wchar uses UTF-8 decoding (FUN_141010f90).
// ============================================================
static int GetGameLanguage() {
    if (!g_gameBase) return 1; // EN
    __try {
        uint8_t lang = *(uint8_t*)(g_gameBase + 0x599772D);
        if (lang > 13) return 1; // unknown → EN
        return (int)lang;
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        return 1; // EN
    }
}

static const char* GetWarehouseTitle() {
    switch (GetGameLanguage()) {
        case  0: return u8"\xEA\xB0\x9C\xEC\x9D\xB8 \xEC\xB0\xBD\xEA\xB3\xA0";   // KR: 개인 창고
        case  1: return "Private Storage";                                            // EN
        case  2: return u8"\xE5\x80\x8B\xE4\xBA\xBA\xE5\x80\x89\xE5\xBA\xAB";     // JP: 個人倉庫
        case  3: return u8"\xD0\x9B\xD0\xB8\xD1\x87\xD0\xBD\xD0\xBE\xD0\xB5 \xD1\x85\xD1\x80\xD0\xB0\xD0\xBD\xD0\xB8\xD0\xBB\xD0\xB8\xD1\x89\xD0\xB5"; // RU
        case  4: return u8"\xC3\x96zel Depo";                                        // TR: Özel Depo
        case  5: return u8"Almac\xC3\xA9n Privado";                                  // ES: Almacén Privado
        case  6: return u8"Almac\xC3\xA9n Privado";                                  // MX: Almacén Privado
        case  7: return u8"Entrep\xC3\xB4t Priv\xC3\xA9";                           // FR: Entrepôt Privé
        case  8: return "Privates Lager";                                             // DE
        case  9: return "Magazzino Privato";                                          // IT
        case 10: return "Prywatny Magazyn";                                           // PL
        case 11: return u8"Armaz\xC3\xA9m Privado";                                  // BR: Armazém Privado
        case 12: return u8"\xE5\x80\x8B\xE4\xBA\xBA\xE5\x80\x89\xE5\xBA\xAB";     // TW: 個人倉庫
        case 13: return u8"\xE4\xB8\xAA\xE4\xBA\xBA\xE4\xBB\x93\xE5\xBA\x93";     // CN: 个人仓库
        default: return "Private Storage";
    }
}

static DWORD ReadHexValue(const char* section, const char* key, DWORD defaultVal, const char* iniPath) {
    char buf[32];
    GetPrivateProfileStringA(section, key, "", buf, sizeof(buf), iniPath);
    if (buf[0] == '\0') return defaultVal;
    return (DWORD)strtoul(buf, nullptr, 16);
}

static void LoadConfig(const char* p) {
    g_enabled = GetPrivateProfileIntA("Settings","Enabled",1,p)!=0;
    g_debugLog = GetPrivateProfileIntA("Settings","DebugLog",0,p)!=0;
    g_hotkey = ReadHexValue("Settings", "Hotkey", VK_F6, p);
    g_modifierKey = ReadHexValue("Settings", "ModifierKey", 0, p);
    g_controllerButton = (WORD)ReadHexValue("Settings", "ControllerButton", 0, p);
    g_controllerModifier = (WORD)ReadHexValue("Settings", "ControllerModifier", 0, p);
    g_reloadKey = ReadHexValue("Settings", "ReloadKey", 0, p);

    // PSButton — configurable PS5/PS4 button for warehouse toggle
    char psBtn[32];
    GetPrivateProfileStringA("Settings", "PSButton", "Share", psBtn, sizeof(psBtn), p);
    g_psButtonEnabled = true;
    if      (_stricmp(psBtn, "Share")    == 0) { g_psButtonByteOff = 1; g_psButtonBitMask = 0x10; }
    else if (_stricmp(psBtn, "Options")  == 0) { g_psButtonByteOff = 1; g_psButtonBitMask = 0x20; }
    else if (_stricmp(psBtn, "Circle")   == 0) { g_psButtonByteOff = 0; g_psButtonBitMask = 0x40; }
    else if (_stricmp(psBtn, "Triangle") == 0) { g_psButtonByteOff = 0; g_psButtonBitMask = 0x80; }
    else if (_stricmp(psBtn, "Square")   == 0) { g_psButtonByteOff = 0; g_psButtonBitMask = 0x10; }
    else if (_stricmp(psBtn, "Cross")    == 0) { g_psButtonByteOff = 0; g_psButtonBitMask = 0x20; }
    else if (_stricmp(psBtn, "L1")       == 0) { g_psButtonByteOff = 1; g_psButtonBitMask = 0x01; }
    else if (_stricmp(psBtn, "R1")       == 0) { g_psButtonByteOff = 1; g_psButtonBitMask = 0x02; }
    else if (_stricmp(psBtn, "L3")       == 0) { g_psButtonByteOff = 1; g_psButtonBitMask = 0x40; }
    else if (_stricmp(psBtn, "R3")       == 0) { g_psButtonByteOff = 1; g_psButtonBitMask = 0x80; }
    else if (_stricmp(psBtn, "Touchpad") == 0) { g_psButtonByteOff = 2; g_psButtonBitMask = 0x02; }
    else if (_stricmp(psBtn, "PS")       == 0) { g_psButtonByteOff = 2; g_psButtonBitMask = 0x01; }
    else if (_stricmp(psBtn, "Mute")     == 0) { g_psButtonByteOff = 2; g_psButtonBitMask = 0x04; }
    else if (_stricmp(psBtn, "none")     == 0) { g_psButtonEnabled = false; }
    else { /* unknown name, default to Share */  g_psButtonByteOff = 1; g_psButtonBitMask = 0x10; }
    Log("PSButton=%s → byteOff=%d bitMask=0x%02X enabled=%d", psBtn, g_psButtonByteOff, g_psButtonBitMask, g_psButtonEnabled);
}

static uintptr_t ScanPattern(const uint8_t* pat, int len) {
    uint8_t* base = (uint8_t*)g_gameBase;
    for (DWORD i = 0; (DWORD)(i+len) <= g_imageSize; i++)
        if (memcmp(base+i, pat, len)==0) return g_gameBase+i;
    return 0;
}

// String-Xref helpers (from QuickMenuHotkeys)
static uintptr_t FindString(const char* str) {
    uint8_t* base = (uint8_t*)g_gameBase;
    int len = (int)strlen(str);
    for (DWORD i = 0; i + len + 1 < g_imageSize; i++) {
        if (base[i] == (uint8_t)str[0] &&
            memcmp(base + i, str, len + 1) == 0)
            return (uintptr_t)(base + i);
    }
    return 0;
}

static uintptr_t FindLEA(uintptr_t targetAddr, uintptr_t afterAddr = 0) {
    uint8_t* base = (uint8_t*)g_gameBase;
    DWORD start = afterAddr > g_gameBase ? (DWORD)(afterAddr - g_gameBase) : 0;
    for (DWORD i = start; i + 7 < g_imageSize; i++) {
        uint8_t* p = base + i;
        if ((p[0] == 0x48 || p[0] == 0x4C) && p[1] == 0x8D) {
            uint8_t modrm = p[2];
            if ((modrm & 0xC7) == 0x05) {
                int32_t disp = *(int32_t*)(p + 3);
                uintptr_t resolved = (uintptr_t)(p + 7) + disp;
                if (resolved == targetAddr)
                    return (uintptr_t)p;
            }
        }
    }
    return 0;
}

static int FindAllCALLsAfter(uintptr_t from, int maxRange,
                              uintptr_t* targets, int maxTargets) {
    uint8_t* start = (uint8_t*)from;
    int count = 0;
    for (int i = 0; i < maxRange && count < maxTargets; i++) {
        if (start[i] == 0xE8) {
            int32_t rel = *(int32_t*)(start + i + 1);
            uintptr_t target = (uintptr_t)(start + i + 5) + rel;
            if (target > g_gameBase && target < g_gameBase + 0x10000000) {
                targets[count++] = target;
                i += 4;
            }
        }
    }
    return count;
}

// Find function start by scanning backwards for function boundary + prolog
static uintptr_t FindFunctionStart(uintptr_t addrInside, int maxBack = 0x1000) {
    for (int i = 1; i < maxBack; i++) {
        uint8_t* p = (uint8_t*)(addrInside - i);
        uint8_t prev = p[-1];
        // Function boundaries: RET (0xC3) or INT3 padding (0xCC)
        if (prev != 0xC3 && prev != 0xCC) continue;
        // Skip consecutive INT3 padding bytes
        if (prev == 0xCC && p[0] == 0xCC) continue;
        // mov [rsp+8], rcx  (48 89 4C 24 08)
        if (p[0] == 0x48 && p[1] == 0x89 && p[2] == 0x4C && p[3] == 0x24 && p[4] == 0x08)
            return (uintptr_t)p;
        // mov [rsp+8], rbx  (48 89 5C 24 08)
        if (p[0] == 0x48 && p[1] == 0x89 && p[2] == 0x5C && p[3] == 0x24 && p[4] == 0x08)
            return (uintptr_t)p;
        // REX push rbp  (40 55)
        if (p[0] == 0x40 && p[1] == 0x55)
            return (uintptr_t)p;
        // sub rsp, imm8  (48 83 EC xx)
        if (p[0] == 0x48 && p[1] == 0x83 && p[2] == 0xEC)
            return (uintptr_t)p;
        // push rbp; mov rbp, rsp  (55 48 89 E5)
        if (p[0] == 0x55 && p[1] == 0x48 && p[2] == 0x89 && p[3] == 0xE5)
            return (uintptr_t)p;
        // push rbp; sub rsp  (55 48 83 EC) or (55 48 81 EC)
        if (p[0] == 0x55 && p[1] == 0x48 && (p[2] == 0x83 || p[2] == 0x81) && p[3] == 0xEC)
            return (uintptr_t)p;
    }
    return 0;
}

static bool InitXInput() {
    const char* dlls[] = { "xinput1_4.dll", "xinput1_3.dll", "xinput9_1_0.dll" };
    for (int i = 0; i < 3; i++) {
        g_hXInput = LoadLibraryA(dlls[i]);
        if (g_hXInput) {
            g_pXInputGetState = (PFN_XInputGetState)GetProcAddress(g_hXInput, "XInputGetState");
            if (g_pXInputGetState) {
                Log("XInput loaded: %s", dlls[i]);
                return true;
            }
            FreeLibrary(g_hXInput);
            g_hXInput = nullptr;
        }
    }
    Log("WARNING: XInput not available");
    return false;
}

// ============================================================
//  Game Hooks
// ============================================================
extern "C" void __fastcall CaptureOnHandler(void* thisPtr, void* rdx) {
    InterlockedIncrement(&g_handlerHitCount);
    if (g_handlerHitCount == 1 && !g_handlerThis) {
        InterlockedExchange64(&g_handlerThis, (LONG64)(uintptr_t)thisPtr);
        Log("CAPTURED warehouse controller via handler: 0x%llX",
            (unsigned long long)(uintptr_t)thisPtr);

        // Resolve panelId dynamically from the handler's sub-object
        // This makes the mod compatible with UI-mods that change panel registration order
        __try {
            uintptr_t sub = *(uintptr_t*)((uint8_t*)thisPtr + 0x08);
            if (sub) {
                uint16_t realId = *(uint16_t*)((uint8_t*)sub + 0x92);
                if (realId != 0xFFFF && realId != 0) {
                    InterlockedExchange(&g_warehousePanelId, (LONG)realId);
                    Log("  Dynamic panelId: 0x%04X", realId);
                }
            }
        } __except(EXCEPTION_EXECUTE_HANDLER) {}
    }

    // Log game-driven handler calls (diagnostics, not used for title fix anymore)
    if (!InterlockedCompareExchange(&g_warehouseActive, 0, 0)) {
        __try {
            uint8_t* cmd = (uint8_t*)rdx;
            uint8_t cmdByte = cmd ? cmd[0] : 0xFF;
            if (g_handlerHitCount <= 20 || cmdByte == 0x15 || cmdByte == 0x0E) {
                Log("  Handler(game): cmd=0x%02X hitCount=%ld",
                    cmdByte, (long)g_handlerHitCount);
            }
            // After game-driven 0x0E, dump the NPC key list to see what keys
            // produce "Privates Lager"
            if (cmdByte == 0x0E) {
                uintptr_t handler = (uintptr_t)thisPtr;
                uintptr_t parent = *(uintptr_t*)(handler + 8);
                if (parent > 0x10000) {
                    uint16_t idx92 = *(uint16_t*)(parent + 0x92);
                    if (idx92 != 0xFFFF) {
                        uintptr_t p50 = *(uintptr_t*)(parent + 0x50);
                        uintptr_t pb0 = *(uintptr_t*)(p50 + 0xb0);
                        uintptr_t pd8 = *(uintptr_t*)(pb0 + 0xd8);
                        uint32_t cap = *(uint32_t*)(pd8 + 8);
                        if ((uint32_t)idx92 < cap) {
                            uintptr_t ns = *(uintptr_t*)(*(uintptr_t*)pd8 + (uintptr_t)idx92 * 8);
                            if (ns > 0x10000) {
                                uintptr_t a8 = *(uintptr_t*)(ns + 0xa8);
                                uintptr_t vo = (a8 > 0x10000) ? *(uintptr_t*)(a8 + 0x10) : 0;
                                if (vo > 0x10000) {
                                    uintptr_t ine = *(uintptr_t*)(vo + 0x120);
                                    if (ine > 0x10000) {
                                        uintptr_t lsp = *(uintptr_t*)(ine + 0x150);
                                        if (lsp > 0x10000) {
                                            uint32_t cnt = *(uint32_t*)(lsp + 8);
                                            uintptr_t dp = *(uintptr_t*)lsp;
                                            Log("  0x0E post: innerNpc=%p list count=%u", (void*)ine, cnt);
                                            uintptr_t gObj = *(uintptr_t*)(g_gameBase + 0x5BBAED8);
                                            uintptr_t sArr = (gObj > 0x10000) ? *(uintptr_t*)(gObj + 0x58) : 0;
                                            if (dp > 0x10000 && cnt > 0 && cnt < 100) {
                                                for (uint32_t i = 0; i < cnt && i < 10; i++) {
                                                    int k = *(int*)(dp + i * 4);
                                                    char* nm = "";
                                                    if (sArr > 0x10000) {
                                                        char* n2 = *(char**)(sArr + (uint32_t)k * 0x10);
                                                        if (n2 > (char*)0x10000 && n2 < (char*)0x7FFFFFFFFFFF)
                                                            nm = n2;
                                                    }
                                                    Log("  0x0E list[%u] key=%d => [%.60s]", i, k, nm);
                                                }
                                            }
                                            // Also check handler+0x110 (NPC ID set by base handler)
                                            uintptr_t npcId110 = *(uintptr_t*)(handler + 0x110);
                                            Log("  0x0E handler+0x110=%llu (0x%llX)",
                                                (unsigned long long)npcId110, (unsigned long long)npcId110);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        } __except(EXCEPTION_EXECUTE_HANDLER) {}
    }

    // Block sub-commands in 0x15 handler when mod opened warehouse
    // (our SetInventory call handles items, skip game's NPC-context commands)
    if (InterlockedCompareExchange(&g_warehouseActive, 0, 0)) {
        __try {
            char* cmd = (char*)rdx;
            if (cmd && *cmd == 0x15) {
                uint32_t* pCount = (uint32_t*)(cmd + 0x10);
                if (*pCount > 0) {
                    Log("  Handler: blocking %u sub-commands", *pCount);
                    *pCount = 0;
                }
            }
        } __except(EXCEPTION_EXECUTE_HANDLER) {}
    }
}

extern "C" void __fastcall CaptureModeSwitcher(void* rcx) {
    if (!g_mainChar && (uintptr_t)rcx > 0x10000000000ULL) {
        InterlockedExchange64(&g_mainChar, (LONG64)(uintptr_t)rcx);
        Log("CAPTURED mainChar: 0x%llX", (unsigned long long)(uintptr_t)rcx);

        // Capture cursorObj via pointer chain: RCX+0x50 → +0x60 → deref → +0x78
        __try {
            uintptr_t container = *(uintptr_t*)((uint8_t*)rcx + 0x50);
            if (container) {
                uintptr_t worldList = *(uintptr_t*)(container + 0x60);
                if (worldList) {
                    uintptr_t world = *(uintptr_t*)worldList;
                    if (world) {
                        uintptr_t cursor = *(uintptr_t*)(world + 0x78);
                        if (cursor > 0x10000000000ULL) {
                            InterlockedExchange64(&g_cursorObj, (LONG64)cursor);
                            Log("CAPTURED cursorObj: 0x%llX", (unsigned long long)cursor);
                        }
                    }
                }
            }
        } __except(EXCEPTION_EXECUTE_HANDLER) {}
    }

    // Game calls ModeSwitcher every frame. While warehouse is open,
    // g_modeSwitchByMod stays 1 so this check is always skipped.
    // Close detection is handled by CanShow (+0x118 flag) and explicit
    // user actions (F6/ESC/Circle/B). This block only fires if
    // g_modeSwitchByMod was unexpectedly 0 (should not happen).
    if (InterlockedCompareExchange(&g_warehouseActive, 0, 0) &&
        !InterlockedCompareExchange(&g_modeSwitchByMod, 0, 0)) {
        Log("  ModeSwitcher: unexpected game close detected, releasing warehouse");
        InterlockedExchange(&g_warehouseActive, 0);
        InterlockedExchange(&g_canShowSeen118, 0);
        InterlockedExchange(&g_modeSwitchByMod, 0);
        uint8_t* mc = (uint8_t*)(uintptr_t)InterlockedCompareExchange64(&g_mainChar, 0, 0);
        if (mc) {
            while (InterlockedCompareExchange(&g_modeByteLock, 1, 0) != 0) { _mm_pause(); }
            memcpy(mc + 0xCB1, g_savedModes, 7);
            memcpy(mc + 0xCB8, g_savedSubtypes, 15);
            InterlockedExchange(&g_modeByteLock, 0);
        }
        if (g_cursorShownByMod && g_fnSetCursorVisible) {
            uintptr_t cursor = (uintptr_t)InterlockedCompareExchange64(&g_cursorObj, 0, 0);
            if (cursor) {
                typedef void (__fastcall *PFN_SCV)(void*, char, char);
                ((PFN_SCV)g_fnSetCursorVisible)((void*)cursor, 0, 1);
            }
            g_cursorShownByMod = false;
        }
    }
}

// ============================================================
//  CanShow Hook
// ============================================================
typedef char (__fastcall *PFN_CanShow)(void*);
static PFN_CanShow g_origCanShow = nullptr;

extern "C" char __fastcall HookedCanShow(void* thisPtr) {
    uintptr_t handler = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);

    // Auto-capture: identify warehouse controller by vtable, not panelId.
    // PanelIds are assigned dynamically and can shift when UI-mods (e.g. No Letterbox)
    // replace uigameconfig2.xml. The vtable address is in the code section and never changes.
    // Also detects save-load when warehouse controller is recreated at a new address.
    if (g_warehouseVtableEntry && (uintptr_t)thisPtr != handler) {
        __try {
            uintptr_t objVtable = *(uintptr_t*)thisPtr;
            bool vtableMatch = false;
            if (g_warehouseVtableStart) {
                // After first capture: only accept exact same vtable
                vtableMatch = (objVtable == g_warehouseVtableStart);
            } else if (objVtable > g_gameBase && objVtable < g_gameBase + g_imageSize &&
                       g_warehouseVtableEntry > objVtable &&
                       (g_warehouseVtableEntry - objVtable) < 0x1000 &&
                       ((g_warehouseVtableEntry - objVtable) % 8) == 0 &&
                       *(uintptr_t*)(objVtable + (g_warehouseVtableEntry - objVtable)) == g_fnHandler) {
                // First capture: verify function pointer + reasonable offset (<0x1000)
                g_warehouseVtableStart = objVtable;
                vtableMatch = true;
            }
            if (vtableMatch) {
                InterlockedExchange64(&g_handlerThis, (LONG64)(uintptr_t)thisPtr);
                handler = (uintptr_t)thisPtr;
                uintptr_t sub = *(uintptr_t*)((uint8_t*)thisPtr + 0x08);
                uint16_t panelId = sub ? *(uint16_t*)((uint8_t*)sub + 0x92) : 0xFFFF;
                if (panelId != 0xFFFF && panelId != 0)
                    InterlockedExchange(&g_warehousePanelId, (LONG)panelId);
                Log("AUTO-CAPTURED warehouse controller: 0x%llX (vtable match, panelId=0x%04X)",
                    (unsigned long long)thisPtr, panelId);
            }
        } __except(EXCEPTION_EXECUTE_HANDLER) {}
    }

    // Fallback: panelId-based auto-capture if vtable not available
    if (!handler && !g_warehouseVtableEntry) {
        __try {
            uintptr_t sub = *(uintptr_t*)((uint8_t*)thisPtr + 0x08);
            if (sub) {
                uint16_t panelId = *(uint16_t*)((uint8_t*)sub + 0x92);
                LONG expectedId = InterlockedCompareExchange(&g_warehousePanelId, 0, 0);
                if (panelId == (uint16_t)expectedId) {
                    InterlockedExchange64(&g_handlerThis, (LONG64)(uintptr_t)thisPtr);
                    handler = (uintptr_t)thisPtr;
                    Log("AUTO-CAPTURED warehouse controller: 0x%llX (panelId=0x%04X)",
                        (unsigned long long)thisPtr, panelId);
                }
            }
        } __except(EXCEPTION_EXECUTE_HANDLER) {}
    }

    if (InterlockedCompareExchange(&g_warehouseActive, 0, 0)) {
        if (handler && (uintptr_t)thisPtr == handler) {
            __try {
                uint8_t activeFlag = *(uint8_t*)((uint8_t*)thisPtr + 0x118);
                if (activeFlag == 1) {
                    // Panel is alive — remember we've seen it active
                    InterlockedExchange(&g_canShowSeen118, 1);
                } else if (activeFlag == 0 && InterlockedCompareExchange(&g_canShowSeen118, 0, 0)) {
                    // +0x118 went from 1→0: game closed the panel (B/Circle/Cancel3)
                    Log("  CanShow: game-initiated close detected (+0x118: 1→0)");
                    InterlockedExchange(&g_warehouseActive, 0);
                    InterlockedExchange(&g_canShowSeen118, 0);
                    InterlockedExchange(&g_modeSwitchByMod, 0);
                    uintptr_t mc = (uintptr_t)InterlockedCompareExchange64(&g_mainChar, 0, 0);
                    if (mc) {
                        while (InterlockedCompareExchange(&g_modeByteLock, 1, 0) != 0) { _mm_pause(); }
                        memcpy((uint8_t*)mc + 0xCB1, g_savedModes, 7);
                        memcpy((uint8_t*)mc + 0xCB8, g_savedSubtypes, 15);
                        InterlockedExchange(&g_modeByteLock, 0);
                    }
                    if (g_cursorShownByMod && g_fnSetCursorVisible) {
                        uintptr_t cursor = (uintptr_t)InterlockedCompareExchange64(&g_cursorObj, 0, 0);
                        if (cursor) {
                            typedef void (__fastcall *PFN_SCV)(void*, char, char);
                            ((PFN_SCV)g_fnSetCursorVisible)((void*)cursor, 0, 1);
                        }
                        g_cursorShownByMod = false;
                    }
                    return g_origCanShow(thisPtr);
                }
            } __except(EXCEPTION_EXECUTE_HANDLER) {}
            return 1;   // WareHouseView: force show
        }
        // Blanket suppress ALL other panels while warehouse is active.
        // Do NOT delegate to origCanShow here — it has internal side-effects
        // (CALL 0x1433af8c0) that corrupt game state and cause the warehouse
        // to reappear during subsequent NPC interactions.
        __try {
            uintptr_t sub = *(uintptr_t*)((uint8_t*)thisPtr + 0x08);
            uint16_t pid = sub ? *(uint16_t*)((uint8_t*)sub + 0x92) : 0xFFFF;
            uint8_t flag118 = *(uint8_t*)((uint8_t*)thisPtr + 0x118);
            if (flag118)
                Log("  CanShow: suppressed panel 0x%04X (+0x118=%d, thisPtr=0x%llX)",
                    pid, flag118, (unsigned long long)thisPtr);
        } __except(EXCEPTION_EXECUTE_HANDLER) {}
        return 0;
    }
    return g_origCanShow(thisPtr);
}

// ============================================================
//  Hook Installation
// ============================================================

// Check if first N bytes contain RIP-relative instructions (ModRM.mod=00, R/M=101)
// that would break when relocated to a trampoline at a different address.
static bool ContainsRipRelative(uint8_t* code, int len) {
    for (int i = 0; i < len - 2; i++) {
        uint8_t b = code[i];
        // Skip REX prefixes (0x40-0x4F)
        if (b >= 0x40 && b <= 0x4F && i + 2 < len) {
            uint8_t op = code[i + 1];
            // Two-byte opcodes with ModRM: LEA, MOV, CMP, etc.
            if (op == 0x8D || op == 0x8B || op == 0x89 || op == 0x3B || op == 0x39 ||
                op == 0x63 || op == 0x0F) {
                uint8_t modrm = code[i + 2];
                if ((modrm & 0xC7) == 0x05)  // mod=00, r/m=101 → RIP-relative
                    return true;
            }
        }
    }
    return false;
}

static bool InstallHook(uintptr_t func, uintptr_t capture, const char* name) {
    uint8_t orig[20]; memcpy(orig, (void*)func, 20);
    if (ContainsRipRelative(orig, 15)) {
        Log("HOOK %s: ABORT — RIP-relative instruction in first 15 bytes (base+0x%llX)",
            name, (unsigned long long)(func - g_gameBase));
        return false;
    }
    void* thunk = VirtualAlloc(nullptr,256,MEM_COMMIT|MEM_RESERVE,PAGE_EXECUTE_READWRITE);
    if (!thunk) return false;
    uint8_t* t = (uint8_t*)thunk;
    uintptr_t ret = func + 15;
    *t++=0x50;*t++=0x51;*t++=0x52;
    *t++=0x41;*t++=0x50;*t++=0x41;*t++=0x51;*t++=0x41;*t++=0x52;*t++=0x41;*t++=0x53;
    *t++=0x48;*t++=0x83;*t++=0xEC;*t++=0x20;
    *t++=0x48;*t++=0x8B;*t++=0x4C;*t++=0x24;*t++=0x48;
    *t++=0x48;*t++=0x8B;*t++=0x54;*t++=0x24;*t++=0x40;
    *t++=0x48;*t++=0xB8; *(uintptr_t*)t=capture; t+=8;
    *t++=0xFF;*t++=0xD0;
    *t++=0x48;*t++=0x83;*t++=0xC4;*t++=0x20;
    *t++=0x41;*t++=0x5B;*t++=0x41;*t++=0x5A;*t++=0x41;*t++=0x59;*t++=0x41;*t++=0x58;
    *t++=0x5A;*t++=0x59;*t++=0x58;
    memcpy(t,orig,15); t+=15;
    *t++=0xFF;*t++=0x25; *(uint32_t*)t=0; t+=4; *(uintptr_t*)t=ret; t+=8;
    DWORD op;
    VirtualProtect((void*)func,15,PAGE_EXECUTE_READWRITE,&op);
    uint8_t* p=(uint8_t*)func;
    p[0]=0xFF;p[1]=0x25; *(uint32_t*)(p+2)=0; *(uintptr_t*)(p+6)=(uintptr_t)thunk; p[14]=0x90;
    VirtualProtect((void*)func,15,op,&op);
    FlushInstructionCache(GetCurrentProcess(),(void*)func,15);
    Log("HOOK %s: OK base+0x%llX",name,(unsigned long long)(func-g_gameBase));
    return true;
}

static bool InstallCanShowHook(uintptr_t func) {
    uint8_t orig[20]; memcpy(orig, (void*)func, 20);
    if (ContainsRipRelative(orig, 14)) {
        Log("HOOK CanShow: ABORT — RIP-relative instruction in first 14 bytes (base+0x%llX)",
            (unsigned long long)(func - g_gameBase));
        return false;
    }
    uint8_t* trampoline = (uint8_t*)VirtualAlloc(nullptr, 64, MEM_COMMIT|MEM_RESERVE, PAGE_EXECUTE_READWRITE);
    if (!trampoline) return false;
    memcpy(trampoline, orig, 14);
    trampoline[14] = 0xFF; trampoline[15] = 0x25;
    *(uint32_t*)(trampoline + 16) = 0;
    *(uintptr_t*)(trampoline + 20) = func + 14;
    g_origCanShow = (PFN_CanShow)trampoline;
    DWORD op;
    VirtualProtect((void*)func, 14, PAGE_EXECUTE_READWRITE, &op);
    uint8_t* p = (uint8_t*)func;
    p[0] = 0xFF; p[1] = 0x25;
    *(uint32_t*)(p + 2) = 0;
    *(uintptr_t*)(p + 6) = (uintptr_t)&HookedCanShow;
    VirtualProtect((void*)func, 14, op, &op);
    FlushInstructionCache(GetCurrentProcess(), (void*)func, 14);
    Log("HOOK CanShow: OK base+0x%llX", (unsigned long long)(func - g_gameBase));
    return true;
}

// ============================================================
//  F6 / Controller: Toggle Warehouse
// ============================================================
static void TriggerWarehouse(bool fromKeyboard = false) {
    uintptr_t mainChar = (uintptr_t)InterlockedCompareExchange64(&g_mainChar, 0, 0);
    if (!mainChar) { Log("NOT READY: mainChar"); return; }

    uint8_t* mc = (uint8_t*)mainChar;
    typedef void (__fastcall *PFN_ModeSwitcher)(void*);
    PFN_ModeSwitcher fnMode = (PFN_ModeSwitcher)g_fnModeSwitcher;

    if (!InterlockedCompareExchange(&g_warehouseActive, 0, 0)) {
        uint8_t curSub = mc[0xCA9];
        if (curSub != 0x0E && curSub != 0x0F) { Log("BLOCKED: unsafe state (sub=0x%02X)", curSub); return; }

        Log("=== OPENING WAREHOUSE ===");
        // Acquire spinlock for mode byte access (prevents race with game thread)
        while (InterlockedCompareExchange(&g_modeByteLock, 1, 0) != 0) { _mm_pause(); }
        memcpy(g_savedModes, mc + 0xCB1, 7);
        memcpy(g_savedSubtypes, mc + 0xCB8, 15);
        memset(mc + 0xCB1, 0, 7);
        memset(mc + 0xCB8, 0, 15);
        mc[0xCB1 + 4] = 1;
        mc[0xCB8 + 5] = 1;
        InterlockedExchange(&g_modeByteLock, 0);

        InterlockedExchange(&g_canShowSeen118, 0);
        InterlockedExchange(&g_warehouseActive, 1);
        g_openTimestamp = GetTickCount64();

        // Pre-activate warehouse handler BEFORE fnMode so the game sees it as the active panel.
        // Without this, stale +0x118=1 on other store panels (IndulgenceView) can cause
        // the game to show the wrong panel during mode switch.
        uintptr_t handler = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);
        if (handler) {
            __try {
                // Set active flag (what CanShow reads)
                *(uint8_t*)(handler + 0x118) = 1;
                // Set visibility bit on sub-object (what scene system reads)
                uintptr_t sub = *(uintptr_t*)((uint8_t*)handler + 0x08);
                if (sub) {
                    uintptr_t linked = *(uintptr_t*)(sub + 0xA8);
                    if (linked) {
                        uintptr_t sceneObj = *(uintptr_t*)(linked + 0x10);
                        if (sceneObj) {
                            *(uint8_t*)(sceneObj + 0x21A) |= 1;
                            Log("  Pre-activated warehouse (+0x118=1, +0x21a bit set)");
                        }
                    }
                }
            } __except(EXCEPTION_EXECUTE_HANDLER) {
                Log("  Pre-activate: partial (only +0x118)");
            }
        }

        __try {
            InterlockedExchange(&g_modeSwitchByMod, 1);
            fnMode((void*)mainChar);
            // NOTE: g_modeSwitchByMod stays 1 while warehouse is open!
            // The game calls ModeSwitcher every frame; keeping this flag
            // prevents CaptureModeSwitcher from mis-detecting those as closes.
            // It gets reset to 0 only when we explicitly close the warehouse.
        } __except(EXCEPTION_EXECUTE_HANDLER) {
            InterlockedExchange(&g_modeSwitchByMod, 0);
            InterlockedExchange(&g_warehouseActive, 0);
            return;
        }

        // Post-open: call handler with empty 0x15 to clear cached NPC state
        // (resets title, donate buttons, inventory from previous NPC interaction)
        if (!handler) handler = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);
        if (handler && g_fnHandler) {
            __try {
                uint8_t cmdPacket[24] = {};
                cmdPacket[0] = 0x15;  // warehouse command, 0 entries → only clearing code runs
                typedef void (__fastcall *PFN_Handler)(void*, void*);
                ((PFN_Handler)g_fnHandler)((void*)handler, (void*)cmdPacket);
                Log("  Handler: cache cleared via empty 0x15");
            } __except(EXCEPTION_EXECUTE_HANDLER) {
                Log("  Handler: cache clear EXCEPTION");
            }
        }

        // Load inventory items
        if (handler && g_fnSetInventory) {
            __try {
                typedef void (__fastcall *PFN_SetInv)(void*, void*);
                ((PFN_SetInv)g_fnSetInventory)((void*)handler, (void*)WAREHOUSE_INIT_STRING);
                Log("  SetInventory called");
            } __except(EXCEPTION_EXECUTE_HANDLER) {
                Log("  SetInventory EXCEPTION");
            }
        }

        // Fix bottom inventory label using verified offset from Ghidra:
        // handler+0x300 = selector-warehouse-inventory-title (.cpp-ware-house-inventory-title)
        // Verified: handler decompilation shows FUN_1433aadf0(handler+0x300, text) for SetWareHouseInventoryName
        if (handler && g_fnSetTitle) {
            typedef uint8_t (__fastcall *PFN_SetTitle)(uintptr_t, const char*);
            PFN_SetTitle setTitle = (PFN_SetTitle)g_fnSetTitle;

            __try {
                uintptr_t bottomLabel = *(uintptr_t*)(handler + 0x300);
                if (bottomLabel) {
                    const char* title = GetWarehouseTitle();
                    setTitle(bottomLabel, title);
                    Log("  Bottom label (+0x300) set: lang=%d", GetGameLanguage());
                }
            } __except(EXCEPTION_EXECUTE_HANDLER) {}

            // === FIX TOP TITLE: SetTitle on handler+0x0E0 ===
            // SCAN found handler+0x0E0.c[0] has a live text setter (bridge+8 != 0).
            // SetTitle will use safe redirect path (like +0x300 bottom label).
            __try {
                uintptr_t topNode = *(uintptr_t*)(handler + 0x0E0);
                if (topNode > 0x10000 && topNode < 0x7FFFFFFFFFFF) {
                    const char* title = GetWarehouseTitle();
                    uint8_t ret = setTitle(topNode, title);
                    Log("  Top title (+0x0E0) set: lang=%d ret=%u", GetGameLanguage(), (unsigned)ret);
                } else {
                    Log("  Top title (+0x0E0) invalid pointer");
                }
            } __except(EXCEPTION_EXECUTE_HANDLER) {
                Log("  Top title (+0x0E0) EXCEPTION");
            }
        }

        // Show mouse cursor for keyboard+mouse players
        // Uses the game's own SetCursorVisible to properly switch input mode
        // (releases ClipCursor, shows cursor, fires InputCursorModeEvent)
        if (fromKeyboard && g_fnSetCursorVisible) {
            uintptr_t cursor = (uintptr_t)InterlockedCompareExchange64(&g_cursorObj, 0, 0);
            if (cursor) {
                typedef void (__fastcall *PFN_SetCursorVisible)(void*, char, char);
                ((PFN_SetCursorVisible)g_fnSetCursorVisible)((void*)cursor, 1, 1);
                g_cursorShownByMod = true;
                Log("  Cursor shown via SetCursorVisible (keyboard trigger)");
            }
        }

        Log("  Warehouse opened (mode=0x%02X sub=0x%02X)", mc[0xCA8], mc[0xCA9]);

    } else {
        Log("=== CLOSING WAREHOUSE ===");
        InterlockedExchange(&g_warehouseActive, 0);

        // Clear stale active flags on warehouse handler to prevent it from
        // appearing during future NPC interactions (origCanShow reads +0x118)
        uintptr_t closeHandler = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);
        if (closeHandler) {
            __try {
                *(uint8_t*)(closeHandler + 0x118) = 0;
                uintptr_t sub = *(uintptr_t*)((uint8_t*)closeHandler + 0x08);
                if (sub) {
                    uintptr_t linked = *(uintptr_t*)(sub + 0xA8);
                    if (linked) {
                        uintptr_t sceneObj = *(uintptr_t*)(linked + 0x10);
                        if (sceneObj) {
                            *(uint8_t*)(sceneObj + 0x21A) &= ~1;
                            Log("  Cleared stale flags (+0x118=0, +0x21a bit cleared)");
                        }
                    }
                }
            } __except(EXCEPTION_EXECUTE_HANDLER) {
                Log("  Cleared +0x118 only (scene obj access failed)");
            }
        }

        while (InterlockedCompareExchange(&g_modeByteLock, 1, 0) != 0) { _mm_pause(); }
        memcpy(mc + 0xCB1, g_savedModes, 7);
        memcpy(mc + 0xCB8, g_savedSubtypes, 15);
        InterlockedExchange(&g_modeByteLock, 0);
        // Hide cursor if we showed it
        if (g_cursorShownByMod && g_fnSetCursorVisible) {
            uintptr_t cursor = (uintptr_t)InterlockedCompareExchange64(&g_cursorObj, 0, 0);
            if (cursor) {
                typedef void (__fastcall *PFN_SetCursorVisible)(void*, char, char);
                ((PFN_SetCursorVisible)g_fnSetCursorVisible)((void*)cursor, 0, 1);
                Log("  Cursor hidden via SetCursorVisible");
            }
            g_cursorShownByMod = false;
        }

        __try {
            InterlockedExchange(&g_modeSwitchByMod, 1);
            fnMode((void*)mainChar);
            InterlockedExchange(&g_modeSwitchByMod, 0);
        } __except(EXCEPTION_EXECUTE_HANDLER) {
            InterlockedExchange(&g_modeSwitchByMod, 0);
        }

        Log("  Warehouse closed (mode=0x%02X sub=0x%02X)", mc[0xCA8], mc[0xCA9]);
    }
}

// ============================================================
//  WndProc + Input
// ============================================================
static volatile LONG g_pendingCircleClose = 0;  // 1 = waiting for Circle release to close

static LRESULT CALLBACK HookedWndProc(HWND h, UINT m, WPARAM w, LPARAM l) {
    if (m==WM_TRIGGER_WAREHOUSE) { TriggerWarehouse((bool)w); return 0; }
    if (InterlockedCompareExchange(&g_warehouseActive, 0, 0) && m==WM_KEYDOWN && w==VK_ESCAPE) {
        PostMessageA(h,WM_TRIGGER_WAREHOUSE,1,0); return 0;
    }
    // --- Raw Input: DualSense / DualShock buttons ---
    if (m == WM_INPUT) {
        ParseSonyButtons(l);

        bool circleDown = g_lastCircle;
        bool psDown     = g_lastPSButton;

        // PSButton rising edge → toggle warehouse open/close
        if (psDown && !g_psButtonWasDown && g_psButtonEnabled) {
            if (InterlockedCompareExchange(&g_warehouseActive, 0, 0)) {
                // Warehouse is open → close it
                Log("PSButton pressed → closing warehouse");
                PostMessageA(h, WM_TRIGGER_WAREHOUSE, 1, 0);
            } else {
                // Warehouse is closed → open it
                Log("PSButton pressed → opening warehouse");
                PostMessageA(h, WM_TRIGGER_WAREHOUSE, 0, 0);
            }
        }
        g_psButtonWasDown = psDown;

        // Circle pressed while warehouse open → mark pending close (don't close yet)
        if (circleDown && !g_circleWasDown && InterlockedCompareExchange(&g_warehouseActive, 0, 0)) {
            Log("Circle pressed → pending close (waiting for release)");
            InterlockedExchange(&g_pendingCircleClose, 1);
        }

        // Circle released after pending close → NOW actually close
        if (!circleDown && g_circleWasDown && InterlockedCompareExchange(&g_pendingCircleClose, 0, 0)) {
            Log("Circle released → closing warehouse now");
            InterlockedExchange(&g_pendingCircleClose, 0);
            PostMessageA(h, WM_TRIGGER_WAREHOUSE, 1, 0);
        }

        g_circleWasDown = circleDown;
    }
    return CallWindowProcA(g_originalWndProc, h, m, w, l);
}

static bool g_keyDown=false; static DWORD g_lastAct=0;
static DWORD WINAPI InputThread(LPVOID) {
    while (true) {
        Sleep(16);
        if (!g_enabled||!g_ready||!g_gameWindow) continue;
        if (GetForegroundWindow()!=g_gameWindow) continue;

        // INI hot-reload (always available, regardless of game state)
        static bool reloadDown = false;
        if (g_reloadKey) {
            bool rd = (GetAsyncKeyState(g_reloadKey)&0x8000)!=0;
            if (rd && !reloadDown) {
                reloadDown = true;
                LoadConfig(g_iniPath);
                Log("INI reloaded (hotkey 0x%02X)", g_reloadKey);
            } else if (!rd) reloadDown = false;
        }

        // Don't poll in unsafe states
        uintptr_t mc = (uintptr_t)InterlockedCompareExchange64(&g_mainChar, 0, 0);
        if (mc && !InterlockedCompareExchange(&g_warehouseActive, 0, 0)) {
            uint8_t curSub = ((uint8_t*)mc)[0xCA9];
            if (curSub != 0x0E && curSub != 0x0F) continue;
        }

        bool trigger = false;
        bool fromKeyboard = false;

        // Keyboard
        if (g_hotkey) {
            bool d=(GetAsyncKeyState(g_hotkey)&0x8000)!=0;
            bool modOk = (g_modifierKey == 0) || (GetAsyncKeyState(g_modifierKey)&0x8000)!=0;
            if (d && modOk && !g_keyDown) {
                g_keyDown=true;
                DWORD now=GetTickCount();
                if (now-g_lastAct>=400) {
                    g_lastAct=now;
                    trigger = true;
                    fromKeyboard = true;
                }
            } else if (!d) g_keyDown=false;
        }

        // Controller: B button always closes warehouse, open requires ControllerEnabled=1
        if (!trigger && g_pXInputGetState) {
            XINPUT_STATE_LOCAL state;
            memset(&state, 0, sizeof(state));
            if (g_pXInputGetState(0, &state) == 0) {
                WORD buttons = state.Gamepad.wButtons;
                WORD pressed = buttons & ~g_prevButtons;  // newly pressed
                WORD released = g_prevButtons & ~buttons; // newly released
                g_prevButtons = buttons;

                // B button closes warehouse on RELEASE (not press) to prevent dodge roll
                if (InterlockedCompareExchange(&g_warehouseActive, 0, 0) && (released & 0x2000)) {
                    trigger = true;
                }
                // Open/toggle with configured button
                else if (g_controllerButton && (pressed & g_controllerButton)) {
                    if (g_controllerModifier == 0 || (buttons & g_controllerModifier)) {
                        DWORD now=GetTickCount();
                        if (now-g_lastAct>=400) {
                            g_lastAct=now;
                            trigger = true;
                        }
                    }
                }
            }
        }

        if (trigger) {
            PostMessageA(g_gameWindow,WM_TRIGGER_WAREHOUSE,fromKeyboard?1:0,0);
        }
    }
    return 0;
}

struct FWD{DWORD p;HWND r;};
static BOOL CALLBACK EWP(HWND h,LPARAM l){FWD*d=(FWD*)l;DWORD p=0;GetWindowThreadProcessId(h,&p);
if(p==d->p&&IsWindowVisible(h)){char t[256];GetWindowTextA(h,t,256);if(t[0]){d->r=h;return FALSE;}}return TRUE;}
static HWND FindGameWindow(){FWD d={GetCurrentProcessId(),nullptr};EnumWindows(EWP,(LPARAM)&d);return d.r;}

// ============================================================
//  Pattern Scanning + Init
// ============================================================
static bool ResolveAddresses() {
    g_fnHandler = 0; g_fnModeSwitcher = 0; g_fnCanShow = 0;
    g_fnSetInventory = 0; g_fnSetTitle = 0;

    // ================================================================
    //  PRIMARY: String cross-reference chain (update-resistant)
    //  Handler → SetInventory, SetTitle, CanShow all derived from it
    // ================================================================

    // Step 1: Find Handler via "ShowPackageCampMoneyList" (unique string, 1 xref in binary)
    uintptr_t strSPCML = FindString("ShowPackageCampMoneyList");
    if (strSPCML) {
        Log("  String 'ShowPackageCampMoneyList' at base+0x%llX", (unsigned long long)(strSPCML - g_gameBase));
        uintptr_t leaAddr = FindLEA(strSPCML);
        if (leaAddr) {
            Log("  LEA at base+0x%llX", (unsigned long long)(leaAddr - g_gameBase));
            g_fnHandler = FindFunctionStart(leaAddr);
        }
    }
    Log("Handler:      %s base+0x%llX (string-xref)", g_fnHandler?"OK":"FAIL",
        g_fnHandler?(unsigned long long)(g_fnHandler-g_gameBase):0);

    // Step 2: Find SetInventory via "SetInventory" string → CALL target in Handler
    if (g_fnHandler) {
        uintptr_t strSetInv = FindString("SetInventory");
        if (strSetInv) {
            // Find LEA to "SetInventory" string within the handler range
            uintptr_t leaAddr = FindLEA(strSetInv, g_fnHandler);
            if (leaAddr && leaAddr < g_fnHandler + 0x1000) {
                // The CALL to FUN_140a638e0 is within ~30 bytes after the strcmp branch
                uintptr_t targets[16];
                int n = FindAllCALLsAfter(leaAddr, 60, targets, 16);
                for (int i = 0; i < n; i++) {
                    // SetInventory is the CALL after strcmp succeeds — it's the larger function
                    // Verify by checking its prolog starts with 40 55 (REX PUSH RBP)
                    uint8_t* p = (uint8_t*)targets[i];
                    if (p[0] == 0x40 && p[1] == 0x55) {
                        g_fnSetInventory = targets[i];
                        break;
                    }
                }
            }
        }
    }
    Log("SetInventory: %s base+0x%llX (string-xref)", g_fnSetInventory?"OK":"FAIL",
        g_fnSetInventory?(unsigned long long)(g_fnSetInventory-g_gameBase):0);

    // Step 3: Find SetTitle via "SetWareHouseInventoryName" string → CALL chain in Handler
    if (g_fnHandler) {
        uintptr_t strSetName = FindString("SetWareHouseInventoryName");
        if (strSetName) {
            uintptr_t leaAddr = FindLEA(strSetName, g_fnHandler);
            if (leaAddr && leaAddr < g_fnHandler + 0x1000) {
                // SetTitle (FUN_1433aadf0) is called further down in this branch (~150 bytes)
                uintptr_t targets[16];
                int n = FindAllCALLsAfter(leaAddr, 200, targets, 16);
                for (int i = 0; i < n; i++) {
                    uint8_t* p = (uint8_t*)targets[i];
                    // SetTitle starts with 40 55 (REX PUSH RBP) and is a large function
                    if (p[0] == 0x40 && p[1] == 0x55 && targets[i] != g_fnSetInventory) {
                        g_fnSetTitle = targets[i];
                        break;
                    }
                }
            }
        }
    }
    Log("SetTitle:     %s base+0x%llX (string-xref)", g_fnSetTitle?"OK":"FAIL",
        g_fnSetTitle?(unsigned long long)(g_fnSetTitle-g_gameBase):0);

    // Step 4: Find CanShow via Handler's vtable (offset +0xE0 from Handler entry)
    if (g_fnHandler) {
        // Handler is registered in a vtable. Find DATA xref to handler address.
        uint8_t* base = (uint8_t*)g_gameBase;
        for (DWORD i = 0; i + 8 <= g_imageSize; i += 8) {
            uintptr_t val = *(uintptr_t*)(base + i);
            if (val == g_fnHandler) {
                // Found vtable entry pointing to Handler. CanShow thunk is at +0xE0
                uintptr_t vtableEntry = g_gameBase + i;
                g_warehouseVtableEntry = vtableEntry;
                uintptr_t canShowThunk = *(uintptr_t*)(vtableEntry + 0xE0);
                if (canShowThunk > g_gameBase && canShowThunk < g_gameBase + g_imageSize) {
                    // Thunk is JMP to real CanShow — resolve if it's a JMP [rip+0]
                    uint8_t* t = (uint8_t*)canShowThunk;
                    if (t[0] == 0xFF && t[1] == 0x25) {
                        int32_t disp = *(int32_t*)(t + 2);
                        g_fnCanShow = *(uintptr_t*)(canShowThunk + 6 + disp);
                    } else if (t[0] == 0xE9) {
                        int32_t rel = *(int32_t*)(t + 1);
                        g_fnCanShow = canShowThunk + 5 + rel;
                    } else {
                        g_fnCanShow = canShowThunk;
                    }
                    Log("  Vtable at base+0x%llX, CanShow thunk at base+0x%llX",
                        (unsigned long long)(vtableEntry - g_gameBase),
                        (unsigned long long)(canShowThunk - g_gameBase));
                    break;
                }
            }
        }
    }
    Log("CanShow:      %s base+0x%llX (vtable)", g_fnCanShow?"OK":"FAIL",
        g_fnCanShow?(unsigned long long)(g_fnCanShow-g_gameBase):0);

    // Step 5: ModeSwitcher — pattern scan + post-validation (no string anchor available)
    static const uint8_t pMS[] = {
        0x48,0x89,0x5C,0x24,0x08, 0x48,0x89,0x6C,0x24,0x10,
        0x48,0x89,0x74,0x24,0x18, 0x57, 0x48,0x81,0xEC,0xA0,0x00,0x00,0x00
    };
    // Scan all matches and validate each (pattern has 9 matches, only 1 references 0xCB1)
    {
        uint8_t* base = (uint8_t*)g_gameBase;
        for (DWORD i = 0; (DWORD)(i + sizeof(pMS)) <= g_imageSize; i++) {
            if (memcmp(base + i, pMS, sizeof(pMS)) == 0) {
                uintptr_t candidate = g_gameBase + i;
                // Validate: the correct ModeSwitcher references offset 0xCB1 within first 0x80 bytes
                bool valid = false;
                uint8_t* fn = (uint8_t*)candidate;
                for (int k = 0; k < 0x80; k++) {
                    if (fn[k] == 0xB1 && fn[k+1] == 0x0C && fn[k+2] == 0x00 && fn[k+3] == 0x00) {
                        // Found 0x00000CB1 displacement (little-endian)
                        valid = true;
                        break;
                    }
                }
                if (valid) {
                    g_fnModeSwitcher = candidate;
                    Log("ModeSwitcher: OK base+0x%llX (pattern+validated, match #%d)",
                        (unsigned long long)(candidate - g_gameBase), i);
                    break;
                }
            }
        }
    }
    if (!g_fnModeSwitcher) Log("ModeSwitcher: FAIL (no validated match)");

    // Step 6: Find SetCursorVisible — called from ModeSwitcher via thunk
    // ModeSwitcher calls it near the end with pattern: CALL thunk → thunk JMPs to real function
    // The call passes (cursorObj, 0, 0) to hide cursor. We search for CALL targets in ModeSwitcher
    // that themselves are thunks (start with JMP or CALL to far address).
    if (g_fnModeSwitcher) {
        uintptr_t targets[32];
        int n = FindAllCALLsAfter(g_fnModeSwitcher, 0x200, targets, 32);
        for (int i = 0; i < n; i++) {
            uint8_t* t = (uint8_t*)targets[i];
            // SetCursorVisible thunk starts with a JMP to the real function (E9 rel32)
            // or is a direct function. The real function does GetClipCursor + ShowCursor.
            // Check if target calls GetClipCursor (imported) within first 0x100 bytes
            uintptr_t subTargets[16];
            int sn = FindAllCALLsAfter(targets[i], 0x100, subTargets, 16);
            for (int j = 0; j < sn; j++) {
                // Follow one more level for thunks
                uint8_t* st = (uint8_t*)subTargets[j];
                if (st[0] == 0xE9) {
                    int32_t rel = *(int32_t*)(st + 1);
                    subTargets[j] = (uintptr_t)(st + 5) + rel;
                }
            }
            // The thunk itself might be a JMP
            if (t[0] == 0xE9) {
                int32_t rel = *(int32_t*)(t + 1);
                uintptr_t realFn = (uintptr_t)(t + 5) + rel;
                // Check if real function references GetClipCursor/EqualRect within 0x80 bytes
                uintptr_t innerCalls[16];
                int in2 = FindAllCALLsAfter(realFn, 0x80, innerCalls, 16);
                // SetCursorVisible is identifiable: it has exactly the pattern of
                // checking param, calling vtable+0x38 or vtable+0x40, then firing event
                // For now, accept the first thunk-JMP target from ModeSwitcher that is
                // in a high address range (the real SetCursorVisible is at 0x152xxxxxx)
                if (realFn > g_gameBase + 0x10000000) {
                    g_fnSetCursorVisible = targets[i];
                    Log("SetCursorVisible: OK base+0x%llX (thunk from ModeSwitcher)",
                        (unsigned long long)(targets[i] - g_gameBase));
                    break;
                }
            }
        }
        if (!g_fnSetCursorVisible) Log("SetCursorVisible: FAIL (not found in ModeSwitcher)");
    }

    // ================================================================
    //  FALLBACK: Old pattern scans if string-xref chain failed
    // ================================================================

    if (!g_fnSetInventory) {
        static const uint8_t pSI[] = {
            0x40,0x55, 0x53, 0x56, 0x57, 0x41,0x54, 0x41,0x55, 0x41,0x56, 0x41,0x57,
            0x48,0x8D,0xAC,0x24,0x18,0xFE,0xFF,0xFF,
            0x48,0x81,0xEC,0xE8,0x02,0x00,0x00
        };
        g_fnSetInventory = ScanPattern(pSI, sizeof(pSI));
        Log("SetInventory: %s base+0x%llX (FALLBACK pattern)", g_fnSetInventory?"OK":"FAIL",
            g_fnSetInventory?(unsigned long long)(g_fnSetInventory-g_gameBase):0);
    }

    if (!g_fnHandler && g_fnSetInventory) {
        // Old handler scan: CMP [RBX],0x15 + SetInventory CALL verify + backward search
        uintptr_t searchStart = g_gameBase;
        while (searchStart < g_gameBase + g_imageSize - 3) {
            uint8_t* s = (uint8_t*)searchStart;
            uintptr_t remaining = g_gameBase + g_imageSize - searchStart;
            uintptr_t cmpAddr = 0;
            for (uintptr_t k = 0; k + 3 <= remaining; k++) {
                if (s[k]==0x80 && s[k+1]==0x3B && s[k+2]==0x15) { cmpAddr = searchStart + k; break; }
            }
            if (!cmpAddr) break;
            bool verified = false;
            for (int i = 0; i < 0x500; i++) {
                uint8_t* p = (uint8_t*)(cmpAddr + i);
                if (p[0] == 0xE8) {
                    int32_t rel = *(int32_t*)(p + 1);
                    uintptr_t target = cmpAddr + i + 5 + rel;
                    if (target == g_fnSetInventory) { verified = true; break; }
                }
            }
            if (verified) {
                g_fnHandler = FindFunctionStart(cmpAddr);
                if (g_fnHandler) break;
            }
            searchStart = cmpAddr + 1;
        }
        Log("Handler:      %s base+0x%llX (FALLBACK pattern)", g_fnHandler?"OK":"FAIL",
            g_fnHandler?(unsigned long long)(g_fnHandler-g_gameBase):0);
    }

    if (!g_fnCanShow) {
        static const uint8_t pCSEnd[] = {
            0x41,0x0F,0xB6,0x81,0x18,0x01,0x00,0x00, 0x48,0x83,0xC4,0x28, 0xC3
        };
        uintptr_t csEnd = ScanPattern(pCSEnd, sizeof(pCSEnd));
        if (csEnd) {
            for (int i = 0; i < 0x100; i++) {
                uint8_t* p = (uint8_t*)(csEnd - i);
                if (p[0]==0x48 && p[1]==0x83 && p[2]==0xEC && p[3]==0x28 &&
                    p[4]==0x48 && p[5]==0x8B && p[6]==0x41 && p[7]==0x08) {
                    g_fnCanShow = csEnd - i; break;
                }
            }
        }
        Log("CanShow:      %s base+0x%llX (FALLBACK pattern)", g_fnCanShow?"OK":"FAIL",
            g_fnCanShow?(unsigned long long)(g_fnCanShow-g_gameBase):0);
    }

    if (!g_fnSetTitle) {
        static const uint8_t pST[] = {
            0x40, 0x55, 0x53, 0x56, 0x57, 0x41, 0x56,
            0x48, 0x8D, 0xAC, 0x24, 0x70, 0xF0, 0xFF, 0xFF,
            0xB8, 0x90, 0x10, 0x00, 0x00
        };
        g_fnSetTitle = ScanPattern(pST, sizeof(pST));
        Log("SetTitle:     %s base+0x%llX (FALLBACK pattern)", g_fnSetTitle?"OK":"FAIL",
            g_fnSetTitle?(unsigned long long)(g_fnSetTitle-g_gameBase):0);
    }

    return g_fnHandler && g_fnModeSwitcher && g_fnCanShow && g_fnSetInventory;
}

static DWORD WINAPI ModThread(LPVOID) {
    for(int i=0;i<120;i++){Sleep(1000);g_gameWindow=FindGameWindow();if(g_gameWindow)break;}
    if(!g_gameWindow)return 0;
    Sleep(10000);

    char dp[MAX_PATH];GetModuleFileNameA(g_hModule,dp,MAX_PATH);
    std::string ip(dp);size_t d=ip.rfind('.');if(d!=std::string::npos)ip=ip.substr(0,d);ip+=".ini";
    strncpy(g_iniPath, ip.c_str(), MAX_PATH-1);
    LoadConfig(g_iniPath);
    if(!g_enabled)return 0;
    if(g_debugLog){std::string lp=ip.substr(0,ip.rfind('.'))+".log";g_logFile=fopen(lp.c_str(),"w");}

    Log("=== Private Storage Anywhere v1.2.0 ===");
    g_gameBase=(uintptr_t)GetModuleHandleA("CrimsonDesert.exe");
    if(!g_gameBase){Log("FATAL: no game base");return 0;}
    MODULEINFO mi;GetModuleInformation(GetCurrentProcess(),(HMODULE)g_gameBase,&mi,sizeof(mi));
    g_imageSize=mi.SizeOfImage;
    Log("Base: 0x%llX  Size: 0x%X  Hotkey: 0x%02X",
        (unsigned long long)g_gameBase, g_imageSize, g_hotkey);

    if(!ResolveAddresses()){Log("FATAL: pattern scan failed");return 0;}

    // Save original bytes before hooking (for cleanup on unload)
    memcpy(g_origHandlerBytes, (void*)g_fnHandler, 15);
    g_hookAddrHandler = g_fnHandler;
    memcpy(g_origModeSwitcherBytes, (void*)g_fnModeSwitcher, 15);
    g_hookAddrModeSwitcher = g_fnModeSwitcher;
    memcpy(g_origCanShowBytes, (void*)g_fnCanShow, 14);
    g_hookAddrCanShow = g_fnCanShow;

    if(!InstallHook(g_fnHandler,(uintptr_t)&CaptureOnHandler,"Handler")) return 0;
    if(!InstallHook(g_fnModeSwitcher,(uintptr_t)&CaptureModeSwitcher,"ModeSwitcher")) return 0;
    if(!InstallCanShowHook(g_fnCanShow)) return 0;

    if (InitXInput()) {
        if (g_controllerButton)
            Log("Controller: button=0x%04X modifier=0x%04X", g_controllerButton, g_controllerModifier);
        else
            Log("Controller: XInput loaded (B to close, no open button configured)");
    }

    SetLastError(0);
    g_originalWndProc=(WNDPROC)SetWindowLongPtrA(g_gameWindow,GWLP_WNDPROC,(LONG_PTR)HookedWndProc);
    if(!g_originalWndProc&&GetLastError()!=0){Log("FATAL: WndProc hook failed (error=%lu)",GetLastError());return 0;}

    // Register for HID Gamepad raw input so we receive WM_INPUT for controllers
    // The game reads HID directly (ReadFile) so no WM_INPUT for gamepads arrives by default
    RAWINPUTDEVICE rid[2] = {};
    // Usage Page 0x01 = Generic Desktop, Usage 0x05 = Game Pad
    rid[0].usUsagePage = 0x01;
    rid[0].usUsage     = 0x05;
    rid[0].dwFlags     = RIDEV_INPUTSINK;  // receive even when not focused
    rid[0].hwndTarget  = g_gameWindow;
    // Usage Page 0x01 = Generic Desktop, Usage 0x04 = Joystick (some controllers report as joystick)
    rid[1].usUsagePage = 0x01;
    rid[1].usUsage     = 0x04;
    rid[1].dwFlags     = RIDEV_INPUTSINK;
    rid[1].hwndTarget  = g_gameWindow;
    if (RegisterRawInputDevices(rid, 2, sizeof(RAWINPUTDEVICE)))
        Log("Raw Input: registered for HID GamePad + Joystick");
    else
        Log("Raw Input: RegisterRawInputDevices FAILED (error=%lu)", GetLastError());

    g_ready=true;
    CreateThread(nullptr,0,InputThread,nullptr,0,nullptr);
    Log("=== READY! Press F6 to open Private Storage from anywhere ===");
    return 0;
}

BOOL APIENTRY DllMain(HMODULE h,DWORD r,LPVOID){
    if(r==DLL_PROCESS_ATTACH){g_hModule=h;DisableThreadLibraryCalls(h);CreateThread(nullptr,0,ModThread,nullptr,0,nullptr);}
    else if(r==DLL_PROCESS_DETACH){
        if(g_gameWindow&&g_originalWndProc)SetWindowLongPtrA(g_gameWindow,GWLP_WNDPROC,(LONG_PTR)g_originalWndProc);
        // Restore original bytes for all game hooks to prevent use-after-free
        DWORD op;
        if (g_hookAddrHandler) {
            VirtualProtect((void*)g_hookAddrHandler, 15, PAGE_EXECUTE_READWRITE, &op);
            memcpy((void*)g_hookAddrHandler, g_origHandlerBytes, 15);
            VirtualProtect((void*)g_hookAddrHandler, 15, op, &op);
            FlushInstructionCache(GetCurrentProcess(), (void*)g_hookAddrHandler, 15);
        }
        if (g_hookAddrModeSwitcher) {
            VirtualProtect((void*)g_hookAddrModeSwitcher, 15, PAGE_EXECUTE_READWRITE, &op);
            memcpy((void*)g_hookAddrModeSwitcher, g_origModeSwitcherBytes, 15);
            VirtualProtect((void*)g_hookAddrModeSwitcher, 15, op, &op);
            FlushInstructionCache(GetCurrentProcess(), (void*)g_hookAddrModeSwitcher, 15);
        }
        if (g_hookAddrCanShow) {
            VirtualProtect((void*)g_hookAddrCanShow, 14, PAGE_EXECUTE_READWRITE, &op);
            memcpy((void*)g_hookAddrCanShow, g_origCanShowBytes, 14);
            VirtualProtect((void*)g_hookAddrCanShow, 14, op, &op);
            FlushInstructionCache(GetCurrentProcess(), (void*)g_hookAddrCanShow, 14);
        }
        if(g_hXInput){FreeLibrary(g_hXInput);g_hXInput=nullptr;}
        if(g_logFile){Log("=== Unloaded (hooks restored) ===");fclose(g_logFile);}
    }
    return TRUE;
}
