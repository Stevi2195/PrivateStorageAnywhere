#include <windows.h>
#include <psapi.h>
#include <intrin.h>
#include <cstdio>
#include <cstring>
#include <string>

// ============================================================
//  Private Storage Anywhere v1.2.5
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
static uintptr_t g_fnSetTitleDirect = 0;  // FUN_1434159c0: UTF-8 aware wchar text setter (bypasses bridge check)
static uintptr_t g_fnSetCursorVisible = 0;  // QOL: hides cursor immediately on warehouse close
static uintptr_t g_warehouseVtableEntry = 0;  // vtable address containing handler — used for auto-capture verification
static uintptr_t g_warehouseVtableStart = 0;  // vtable start of warehouse class — set on first successful capture
static uint32_t  g_modalDialogOff = 0;     // handler+N stores active dialog pointer (0x338 in current build, was 0x240)
static uintptr_t g_langByteAddr = 0;      // address of language byte (resolved dynamically from Steam API init function)

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
// NOTE: g_cursorShownByMod removed — not needed, we always hide cursor on close
static volatile LONG g_modeByteLock = 0;  // Spinlock for mode byte read/write
static volatile LONG g_modeSwitchByMod = 0;  // 1 when WE call fnMode, 0 otherwise
static volatile ULONGLONG g_openTimestamp = 0;  // GetTickCount64 at warehouse open (grace period)
static volatile LONG64 g_lastModalPassed = 0;   // ModalMessageView addr when ESC was last passed to game for a modal

// Forward declaration (defined later in Utilities section)
static void Log(const char* fmt, ...);

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

// CRC32 of a file (for detecting modded game files in logs)
static uint32_t FileCRC32(const char* path) {
    static const uint32_t table[256] = {
        0x00000000,0x77073096,0xEE0E612C,0x990951BA,0x076DC419,0x706AF48F,0xE963A535,0x9E6495A3,
        0x0EDB8832,0x79DCB8A4,0xE0D5E91B,0x97D2D988,0x09B64C2B,0x7EB17CBF,0xE7B82D09,0x90BF1D9F,
        0x1DB71064,0x6AB020F2,0xF3B97148,0x84BE41DE,0x1ADAD47D,0x6DDDE4EB,0xF4D4B551,0x83D385C7,
        0x136C9856,0x646BA8C0,0xFD62F97A,0x8A65C9EC,0x14015C4F,0x63066CD9,0xFA0F3D63,0x8D080DF5,
        0x3B6E20C8,0x4C69105E,0xD56041E4,0xA2677172,0x3C03E4D1,0x4B04D447,0xD20D85FD,0xA50AB56B,
        0x35B5A8FA,0x42B2986C,0xDBBBC9D6,0xACBCF940,0x32D86CE3,0x45DF5C75,0xDCD60DCF,0xABD13D59,
        0x26D930AC,0x51DE003A,0xC8D75180,0xBFD06116,0x21B4F0B5,0x56B3C423,0xCFBA9599,0xB8BDA50F,
        0x2802B89E,0x5F058808,0xC60CD9B2,0xB10BE924,0x2F6F7C87,0x58684C11,0xC1611DAB,0xB6662D3D,
        0x76DC4190,0x01DB7106,0x98D220BC,0xEFD5102A,0x71B18589,0x06B6B51F,0x9FBFE4A5,0xE8B8D433,
        0x7807C9A2,0x0F00F934,0x9609A88E,0xE10E9818,0x7F6A0D6B,0x086D3D2D,0x91646C97,0xE6635C01,
        0x6B6B51F4,0x1C6C6162,0x856530D8,0xF262004E,0x6C0695ED,0x1B01A57B,0x8208F4C1,0xF50FC457,
        0x65B0D9C6,0x12B7E950,0x8BBEB8EA,0xFCB9887C,0x62DD1DDF,0x15DA2D49,0x8CD37CF3,0xFBD44C65,
        0x4DB26158,0x3AB551CE,0xA3BC0074,0xD4BB30E2,0x4ADFA541,0x3DD895D7,0xA4D1C46D,0xD3D6F4FB,
        0x4369E96A,0x346ED9FC,0xAD678846,0xDA60B8D0,0x44042D73,0x33031DE5,0xAA0A4C5F,0xDD0D7822,
        0x5005713C,0x270241AA,0xBE0B1010,0xC90C2086,0x5768B525,0x206F85B3,0xB966D409,0xCE61E49F,
        0x5EDEF90E,0x29D9C998,0xB0D09822,0xC7D7A8B4,0x59B33D17,0x2EB40D81,0xB7BD5C3B,0xC0BA6CAD,
        0xEDB88320,0x9ABFB3B6,0x03B6E20C,0x74B1D29A,0xEAD54739,0x9DD277AF,0x04DB2615,0x73DC1683,
        0xE3630B12,0x94643B84,0x0D6D6A3E,0x7A6A5AA8,0xE40ECF0B,0x9309FF9D,0x0A00AE27,0x7D079EB1,
        0xF00F9344,0x8708A3D2,0x1E01F268,0x6906C2FE,0xF762575D,0x806567CB,0x196C3671,0x6E6B06E7,
        0xFED41B76,0x89D32BE0,0x10DA7A5A,0x67DD4ACC,0xF9B9DF6F,0x8EBEEFF9,0x17B7BE43,0x60B08ED5,
        0xD6D6A3E8,0xA1D1937E,0x38D8C2C4,0x4FDFF252,0xD1BB67F1,0xA6BC5767,0x3FB506DD,0x48B2364B,
        0xD80D2BDA,0xAF0A1B4C,0x36034AF6,0x41047A60,0xDF60EFC3,0xA867DF55,0x316E8EEF,0x4669BE79,
        0xCB61B38C,0xBC66831A,0x256FD2A0,0x5268E236,0xCC0C7795,0xBB0B4703,0x220216B9,0x5505262F,
        0xC5BA3BBE,0xB2BD0B28,0x2BB45A92,0x5CB36A04,0xC2D7FFA7,0xB5D0CF31,0x2CD99E8B,0x5BDEAE1D,
        0x9B64C2B0,0xEC63F226,0x756AA39C,0x026D930A,0x9C0906A9,0xEB0E363F,0x72076785,0x05005713,
        0x95BF4A82,0xE2B87A14,0x7BB12BAE,0x0CB61B38,0x92D28E9B,0xE5D5BE0D,0x7CDCEFB7,0x0BDBDF21,
        0x86D3D2D4,0xF1D4E242,0x68DDB3F6,0x1FDA836E,0x81BE16CD,0xF6B9265B,0x6FB077E1,0x18B74777,
        0x88085AE6,0xFF0F6B70,0x66063BCA,0x11010B5C,0x8F659EFF,0xF862AE69,0x616BFFD3,0x166CCF45,
        0xA00AE278,0xD70DD2EE,0x4E048354,0x3903B3C2,0xA7672661,0xD06016F7,0x4969474D,0x3E6E77DB,
        0xAED16A4A,0xD9D65ADC,0x40DF0B66,0x37D83BF0,0xA9BCAE53,0xDEBB9EC5,0x47B2CF7F,0x30B5FFE9,
        0xBDBDF21C,0xCABAC28A,0x53B39330,0x24B4A3A6,0xBAD03605,0xCDD706FF,0x54DE5729,0x23D967BF,
        0xB3667A2E,0xC4614AB8,0x5D681B02,0x2A6F2B94,0xB40BBE37,0xC30C8EA1,0x5A05DF1B,0x2D02EF8D
    };
    FILE* f = fopen(path, "rb");
    if (!f) return 0;
    uint32_t crc = 0xFFFFFFFF;
    uint8_t buf[4096];
    size_t n;
    while ((n = fread(buf, 1, sizeof(buf), f)) > 0)
        for (size_t i = 0; i < n; i++)
            crc = table[(crc ^ buf[i]) & 0xFF] ^ (crc >> 8);
    fclose(f);
    return crc ^ 0xFFFFFFFF;
}

// ============================================================
//  Localization — read game language and return translated title
//  Language byte is resolved dynamically via FindLanguageByte():
//    1. FindString("koreana") → Steam language string (index 0)
//    2. Scan .rdata for pointer to "koreana" → language table start
//    3. Find code referencing the table → Steam API init function
//    4. Scan forward for MOV byte [rip+disp32], reg → language byte write
//  SetTitle (FUN_1433ab4b0) stores text as raw char bytes in nodes.
//  Only the bridge/redirect path (FUN_1434159c0 via node+0xA8)
//  properly decodes UTF-8 to wchar_t (via FUN_141010f90).
//  When no bridge exists, the renderer zero-extends each byte,
//  garbling multi-byte UTF-8 (Korean/CJK/Cyrillic/accented chars).
//  Fix: after SetTitle, call SetTitleDirect on node renderers.
// ============================================================
static int GetGameLanguage() {
    if (!g_langByteAddr) return 1; // EN
    __try {
        uint8_t lang = *(uint8_t*)g_langByteAddr;
        if (lang > 13) return 1; // unknown → EN
        return (int)lang;
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        return 1; // EN
    }
}

static const char* GetWarehouseTitle() {
    // NOTE: Do NOT use u8"" prefix with \x hex escapes!
    // MSVC /utf-8 + u8"" double-encodes bytes > 0x7F (\xEA → C3 AA instead of EA).
    // Plain "" with \x escapes produces the raw bytes we need.
    switch (GetGameLanguage()) {
        case  0: return "\xEA\xB0\x9C\xEC\x9D\xB8 \xEC\xB0\xBD\xEA\xB3\xA0";     // KR: 개인 창고
        case  1: return "Private Storage";                                            // EN
        case  2: return "\xE5\x80\x8B\xE4\xBA\xBA\xE5\x80\x89\xE5\xBA\xAB";       // JP: 個人倉庫
        case  3: return "\xD0\x9B\xD0\xB8\xD1\x87\xD0\xBD\xD0\xBE\xD0\xB5 \xD1\x85\xD1\x80\xD0\xB0\xD0\xBD\xD0\xB8\xD0\xBB\xD0\xB8\xD1\x89\xD0\xB5"; // RU
        case  4: return "\xC3\x96zel Depo";                                          // TR: Özel Depo
        case  5: return "Almac\xC3\xA9n Privado";                                    // ES: Almacén Privado
        case  6: return "Almac\xC3\xA9n Privado";                                    // MX: Almacén Privado
        case  7: return "Entrep\xC3\xB4t Priv\xC3\xA9";                             // FR: Entrepôt Privé
        case  8: return "Privates Lager";                                             // DE
        case  9: return "Magazzino Privato";                                          // IT
        case 10: return "Prywatny Magazyn";                                           // PL
        case 11: return "Armaz\xC3\xA9m Privado";                                    // BR: Armazém Privado
        case 12: return "\xE5\x80\x8B\xE4\xBA\xBA\xE5\x80\x89\xE5\xBA\xAB";       // TW: 個人倉庫
        case 13: return "\xE4\xB8\xAA\xE4\xBA\xBA\xE4\xBB\x93\xE5\xBA\x93";       // CN: 个人仓库
        default: return "Private Storage";
    }
}

// ============================================================
//  UTF-8 title fix — call SetTitleDirect (FUN_1434159c0) on
//  renderers found via bridge chain for proper UTF-8→wchar_t.
// ============================================================
static bool IsAscii(const char* s) {
    for (; *s; s++)
        if ((unsigned char)*s > 0x7F) return false;
    return true;
}

// Walk a UI node tree and call SetTitleDirect on any renderer found
// through the bridge chain: node+0xA8 → bridge → *(bridge+8) → renderer.
static bool SetTitleOnRenderer(uintptr_t node, const char* utf8Title, int depth) {
    if (!node || depth > 5) return false;
    __try {
        uintptr_t bridge = *(uintptr_t*)(node + 0xA8);
        if (bridge > 0x10000 && bridge < 0x7FFFFFFFFFFF) {
            uintptr_t renderer = *(uintptr_t*)(bridge + 8);
            if (renderer > 0x10000 && renderer < 0x7FFFFFFFFFFF) {
                if (g_fnSetTitleDirect) {
                    typedef uint8_t (__fastcall *PFN_STD)(uintptr_t, const char*, uint64_t, uint64_t);
                    ((PFN_STD)g_fnSetTitleDirect)(renderer, utf8Title, 0, 0);
                    Log("    SetTitleOnRenderer: OK depth=%d renderer=0x%llX",
                        depth, (unsigned long long)renderer);
                    return true;
                }
            }
        }
        // Recurse into children
        int32_t childCount = *(int32_t*)(node + 0x38);
        if (childCount > 0 && childCount < 100) {
            uintptr_t childArr = *(uintptr_t*)(node + 0x30);
            if (childArr > 0x10000 && childArr < 0x7FFFFFFFFFFF) {
                for (int i = 0; i < childCount; i++) {
                    uintptr_t child = *(uintptr_t*)(childArr + i * 8);
                    if (child > 0x10000 && child < 0x7FFFFFFFFFFF) {
                        if (SetTitleOnRenderer(child, utf8Title, depth + 1))
                            return true;
                    }
                }
            }
        }
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        Log("    SetTitleOnRenderer: EXCEPTION depth=%d", depth);
    }
    return false;
}

// Read the active modal dialog pointer from the handler struct.
// Offset found dynamically from the move-item handler's code at init.
static uintptr_t ReadModalDialog(uintptr_t handler) {
    if (!g_modalDialogOff) return 0;
    __try {
        return *(uintptr_t*)(handler + g_modalDialogOff);
    } __except(EXCEPTION_EXECUTE_HANDLER) { return 0; }
}

// Check if a NEW sub-dialog (quantity/confirm) is visible that we haven't dismissed yet.
// The ModalMessageView address changes each time a dialog opens.
// After we pass ESC to the game once (dismissing it), we record the address so that
// further ESC presses don't keep passing through (children cleanup is async).
static bool IsNewModalDialogVisible() {
    uintptr_t handler = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);
    if (!handler) return false;
    __try {
        uintptr_t modalView = ReadModalDialog(handler);
        if (modalView > 0x10000 && modalView < 0x7FFFFFFFFFFF) {
            uint32_t childCount = *(uint32_t*)(modalView + 0x30);
            if (childCount == 0) {
                // Children cleaned up — clear tracking so next modal is detected fresh
                InterlockedExchange64(&g_lastModalPassed, 0);
                return false;
            }
            // children > 0: is this a modal we already passed ESC for?
            uintptr_t lastPassed = (uintptr_t)InterlockedCompareExchange64(&g_lastModalPassed, 0, 0);
            if (lastPassed == modalView) {
                // Same modal view, already handled — async cleanup still pending
                return false;
            }
            return true;  // New modal, not yet dismissed
        }
    } __except(EXCEPTION_EXECUTE_HANDLER) {}
    InterlockedExchange64(&g_lastModalPassed, 0);
    return false;
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
    }
}

// ============================================================
//  CanShow Hook
// ============================================================
typedef char (__fastcall *PFN_CanShow)(void*);
static PFN_CanShow g_origCanShow = nullptr;

extern "C" char __fastcall HookedCanShow(void* thisPtr) {
    uintptr_t handler = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);

    // Auto-capture: identify warehouse controller by exact vtable match.
    // g_warehouseVtableStart is resolved during init via RTTI scan — it's the unique
    // vtable for UIGamePlayControlRootWarehouse2.  No offset math, no false positives.
    // Also detects save-load when warehouse controller is recreated at a new address.
    if (g_warehouseVtableStart && (uintptr_t)thisPtr != handler) {
        __try {
            uintptr_t objVtable = *(uintptr_t*)thisPtr;
            if (objVtable == g_warehouseVtableStart) {
                InterlockedExchange64(&g_handlerThis, (LONG64)(uintptr_t)thisPtr);
                handler = (uintptr_t)thisPtr;
                uintptr_t sub = *(uintptr_t*)((uint8_t*)thisPtr + 0x08);
                uint16_t panelId = sub ? *(uint16_t*)((uint8_t*)sub + 0x92) : 0xFFFF;
                if (panelId != 0xFFFF && panelId != 0)
                    InterlockedExchange(&g_warehousePanelId, (LONG)panelId);
                Log("AUTO-CAPTURED warehouse controller: 0x%llX (exact vtable, panelId=0x%04X)",
                    (unsigned long long)thisPtr, panelId);
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
        InterlockedExchange64(&g_lastModalPassed, 0);
        InterlockedExchange(&g_warehouseActive, 1);
        g_openTimestamp = GetTickCount64();

        // Activate warehouse panel via the game's own base-class handler (command 0x0e).
        // This properly sets +0x118, attaches the scene object, and calls the
        // scene registration functions (FUN_1433c4100 + thunk_FUN_1558a7380).
        // Manual +0x118/+0x21A setting is no longer sufficient after the game update.
        uintptr_t handler = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);
        if (handler && g_fnHandler) {
            __try {
                uint8_t showPacket[24] = {};
                showPacket[0] = 0x0e;  // base-class "show panel" command
                typedef void (__fastcall *PFN_Handler)(void*, void*);
                ((PFN_Handler)g_fnHandler)((void*)handler, (void*)showPacket);
                Log("  Panel shown via 0x0e command");
            } __except(EXCEPTION_EXECUTE_HANDLER) {
                Log("  Panel show via 0x0e EXCEPTION, falling back to manual");
                __try {
                    *(uint8_t*)(handler + 0x118) = 1;
                } __except(EXCEPTION_EXECUTE_HANDLER) {}
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

        // NOTE: The old 0x15 cache-clear was removed. After the game update, the
        // 0x15 handler path dereferences sub-objects at handler+0x2c8/0x2d0/0x2f8
        // that are only initialized after NPC interaction, causing a crash.
        // SetInventory below overwrites inventory data completely, and titles
        // are set explicitly afterward, so the cache-clear is unnecessary.
        if (!handler) handler = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);

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
        // Verified: handler decompilation shows FUN_1433ab4b0(handler+0x300, text) for SetWareHouseInventoryName
        if (handler && g_fnSetTitle) {
            typedef uint8_t (__fastcall *PFN_SetTitle)(uintptr_t, const char*);
            PFN_SetTitle setTitle = (PFN_SetTitle)g_fnSetTitle;
            const char* title = GetWarehouseTitle();
            bool needUtf8Fix = !IsAscii(title);

            __try {
                uintptr_t bottomLabel = *(uintptr_t*)(handler + 0x300);
                if (bottomLabel) {
                    setTitle(bottomLabel, title);
                    Log("  Bottom label (+0x300) set: lang=%d needFix=%d", GetGameLanguage(), needUtf8Fix);
                    // For non-ASCII titles: ensure the renderer has correct
                    // wchar_t text.  SetTitle's direct path stores raw UTF-8
                    // bytes which the renderer zero-extends (garbling CJK/accented).
                    // SetTitleOnRenderer calls FUN_1434159c0 which properly
                    // decodes UTF-8 → wchar_t via FUN_141010f90.
                    if (needUtf8Fix) {
                        bool fixed = SetTitleOnRenderer(bottomLabel, title, 0);
                        Log("  Bottom label UTF-8 fix: %s", fixed ? "OK" : "no renderer found");
                    }
                }
            } __except(EXCEPTION_EXECUTE_HANDLER) {}

            // === FIX TOP TITLE: SetTitle on handler+0x0E0 ===
            __try {
                uintptr_t topNode = *(uintptr_t*)(handler + 0x0E0);
                if (topNode > 0x10000 && topNode < 0x7FFFFFFFFFFF) {
                    uint8_t ret = setTitle(topNode, title);
                    Log("  Top title (+0x0E0) set: lang=%d ret=%u", GetGameLanguage(), (unsigned)ret);
                    if (needUtf8Fix) {
                        bool fixed = SetTitleOnRenderer(topNode, title, 0);
                        Log("  Top title UTF-8 fix: %s", fixed ? "OK" : "no renderer found");
                    }
                } else {
                    Log("  Top title (+0x0E0) invalid pointer");
                }
            } __except(EXCEPTION_EXECUTE_HANDLER) {
                Log("  Top title (+0x0E0) EXCEPTION");
            }

        }

        Log("  Warehouse opened (mode=0x%02X sub=0x%02X)", mc[0xCA8], mc[0xCA9]);

    } else {
        Log("=== CLOSING WAREHOUSE ===");
        InterlockedExchange(&g_warehouseActive, 0);

        // Hide warehouse panel via the game's base-class handler (command 0x0f).
        // This properly clears +0x118, detaches the scene object, and calls
        // scene deregistration — symmetric to the 0x0e show command on open.
        uintptr_t closeHandler = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);
        if (closeHandler && g_fnHandler) {
            __try {
                uint8_t hidePacket[24] = {};
                hidePacket[0] = 0x0f;  // base-class "hide panel" command
                typedef void (__fastcall *PFN_Handler)(void*, void*);
                ((PFN_Handler)g_fnHandler)((void*)closeHandler, (void*)hidePacket);
                Log("  Panel hidden via 0x0f command");
            } __except(EXCEPTION_EXECUTE_HANDLER) {
                // Fallback: manual cleanup
                __try {
                    *(uint8_t*)(closeHandler + 0x118) = 0;
                } __except(EXCEPTION_EXECUTE_HANDLER) {}
                Log("  Panel hide via 0x0f EXCEPTION, manual fallback");
            }
        } else if (closeHandler) {
            __try {
                *(uint8_t*)(closeHandler + 0x118) = 0;
                Log("  Cleared +0x118 manually (no handler func)");
            } __except(EXCEPTION_EXECUTE_HANDLER) {}
        }

        while (InterlockedCompareExchange(&g_modeByteLock, 1, 0) != 0) { _mm_pause(); }
        memcpy(mc + 0xCB1, g_savedModes, 7);
        memcpy(mc + 0xCB8, g_savedSubtypes, 15);
        InterlockedExchange(&g_modeByteLock, 0);

        // QOL: Hide cursor immediately when closing warehouse
        if (g_fnSetCursorVisible) {
            uintptr_t cursor = (uintptr_t)InterlockedCompareExchange64(&g_cursorObj, 0, 0);
            if (cursor) {
                __try {
                    typedef void (__fastcall *PFN_SetCursorVisible)(void*, char, char);
                    ((PFN_SetCursorVisible)g_fnSetCursorVisible)((void*)cursor, 0, 1);
                    Log("  Cursor hidden via SetCursorVisible");
                } __except(EXCEPTION_EXECUTE_HANDLER) {}
            }
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
        if (IsNewModalDialogVisible()) {
            // Record which modal we're dismissing so next ESC closes warehouse
            uintptr_t handler = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);
            if (handler) {
                __try {
                    uintptr_t mv = ReadModalDialog(handler);
                    InterlockedExchange64(&g_lastModalPassed, (LONG64)mv);
                } __except(EXCEPTION_EXECUTE_HANDLER) {}
            }
            Log("ESC: sub-dialog active, passing to game");
            return CallWindowProcA(g_originalWndProc, h, m, w, l);
        }
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
                // Warehouse is open → close modal first, or close warehouse
                if (IsNewModalDialogVisible()) {
                    Log("PSButton pressed → sub-dialog active, ignoring close");
                } else {
                    Log("PSButton pressed → closing warehouse");
                    PostMessageA(h, WM_TRIGGER_WAREHOUSE, 1, 0);
                }
            } else {
                // Warehouse is closed → open it
                Log("PSButton pressed → opening warehouse");
                PostMessageA(h, WM_TRIGGER_WAREHOUSE, 0, 0);
            }
        }
        g_psButtonWasDown = psDown;

        // Circle pressed while warehouse open → mark pending close (don't close yet)
        if (circleDown && !g_circleWasDown && InterlockedCompareExchange(&g_warehouseActive, 0, 0)) {
            if (IsNewModalDialogVisible()) {
                Log("Circle pressed → sub-dialog active, ignoring");
            } else {
                Log("Circle pressed → pending close (waiting for release)");
                InterlockedExchange(&g_pendingCircleClose, 1);
            }
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
                    if (IsNewModalDialogVisible()) {
                        Log("B button → sub-dialog active, ignoring");
                    } else {
                        trigger = true;
                    }
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

static HWND FindGameWindow(){
    DWORD myPid=GetCurrentProcessId();
    HWND h=nullptr;
    while((h=FindWindowExW(nullptr,h,L"WindowsLauncherClassName",L"Crimson Desert"))!=nullptr){
        DWORD pid=0;GetWindowThreadProcessId(h,&pid);
        if(pid==myPid)return h;
    }
    return nullptr;
}

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

    // Step 3b: Find SetTitleDirect (FUN_1434159c0) from inside SetTitle.
    // SetTitle checks node+0xA8 (bridge). If bridge+8 (renderer) exists,
    // it calls SetTitleDirect(renderer, text) — which does proper UTF-8→wchar.
    // In the assembly: 1st E8 CALL = __chkstk, 2nd E8 CALL = SetTitleDirect.
    if (g_fnSetTitle) {
        uint8_t* p = (uint8_t*)g_fnSetTitle;
        int callNum = 0;
        for (int i = 0; i < 120; i++) {
            if (p[i] == 0xE8) {
                int32_t rel = *(int32_t*)(p + i + 1);
                uintptr_t target = (uintptr_t)(p + i + 5) + rel;
                if (target > g_gameBase && target < g_gameBase + g_imageSize) {
                    callNum++;
                    if (callNum == 2) {
                        g_fnSetTitleDirect = target;
                        break;
                    }
                }
                i += 4; // skip rel32
            }
        }
    }
    Log("SetTitleDir:  %s base+0x%llX (SetTitle internal)",
        g_fnSetTitleDirect?"OK":"FAIL",
        g_fnSetTitleDirect?(unsigned long long)(g_fnSetTitleDirect-g_gameBase):0);

    // Step 4: Find CanShow via Handler's vtable (update-proof — scans all vtable entries)
    // CanShow signature: contains MOVZX reg, byte [reg+0x118] (reads the active flag).
    // We find ALL data references to g_fnHandler (could be in vtables, reloc tables, etc.),
    // verify each is a real vtable (adjacent entries are valid code pointers), then scan
    // the vtable for a function matching the CanShow signature.
    if (g_fnHandler) {
        uint8_t* base = (uint8_t*)g_gameBase;
        for (DWORD i = 0; i + 8 <= g_imageSize && !g_fnCanShow; i += 8) {
            if (*(uintptr_t*)(base + i) != g_fnHandler) continue;
            uintptr_t vtableEntry = g_gameBase + i;
            // Verify this is a real vtable: at least 4 adjacent entries should be valid code pointers
            int validCount = 0;
            for (int check = -4; check <= 4; check++) {
                uintptr_t addr = vtableEntry + check * 8;
                if (addr < g_gameBase || addr >= g_gameBase + g_imageSize - 8) continue;
                uintptr_t ptr = *(uintptr_t*)addr;
                if (ptr > g_gameBase && ptr < g_gameBase + g_imageSize) validCount++;
            }
            if (validCount < 4) continue;  // not a real vtable, skip
            if (!g_warehouseVtableEntry) g_warehouseVtableEntry = vtableEntry;
            // Scan vtable entries around the handler (±0x800 = up to 256 entries each way)
            uintptr_t vtableBase = (vtableEntry > g_gameBase + 0x800) ? vtableEntry - 0x800 : g_gameBase;
            uintptr_t vtableEnd = vtableEntry + 0x800;
            if (vtableEnd > g_gameBase + g_imageSize - 8) vtableEnd = g_gameBase + g_imageSize - 8;
            for (uintptr_t v = vtableBase; v <= vtableEnd && !g_fnCanShow; v += 8) {
                uintptr_t candidate = *(uintptr_t*)v;
                if (candidate <= g_gameBase || candidate >= g_gameBase + g_imageSize) continue;
                if (candidate == g_fnHandler) continue;
                // Resolve thunks (JMP [rip+disp32] or E9 rel32)
                uintptr_t resolved = candidate;
                uint8_t* t = (uint8_t*)candidate;
                if (t[0] == 0xFF && t[1] == 0x25) {
                    int32_t disp = *(int32_t*)(t + 2);
                    resolved = *(uintptr_t*)(candidate + 6 + disp);
                } else if (t[0] == 0xE9) {
                    int32_t rel = *(int32_t*)(t + 1);
                    resolved = candidate + 5 + rel;
                }
                if (resolved <= g_gameBase || resolved >= g_gameBase + g_imageSize) continue;
                // Check CanShow signature: MOVZX reg, byte [reg+0x118] anywhere in first 0x200 bytes
                // Encoding: (optional REX 41-44) 0F B6 modrm 18 01 00 00, modrm mod=10 (disp32)
                uint8_t* fn = (uint8_t*)resolved;
                for (int j = 0; j < 0x200; j++) {
                    bool found = false;
                    if (fn[j] == 0x0F && fn[j+1] == 0xB6 &&
                        (fn[j+2] & 0xC0) == 0x80 &&
                        *(uint32_t*)(fn + j + 3) == 0x118) {
                        found = true;
                    }
                    if (!found && (fn[j] & 0xFC) == 0x40 &&  // any REX prefix (40-4F)
                        fn[j+1] == 0x0F && fn[j+2] == 0xB6 &&
                        (fn[j+3] & 0xC0) == 0x80 &&
                        *(uint32_t*)(fn + j + 4) == 0x118) {
                        found = true;
                    }
                    if (found) {
                        g_fnCanShow = resolved;
                        g_warehouseVtableEntry = vtableEntry;
                        Log("  Vtable at base+0x%llX, CanShow at base+0x%llX (vtable offset 0x%llX)",
                            (unsigned long long)(vtableEntry - g_gameBase),
                            (unsigned long long)(resolved - g_gameBase),
                            (unsigned long long)(v - vtableEntry));
                        break;
                    }
                }
            }
        }
    }
    Log("CanShow:      %s base+0x%llX (vtable)", g_fnCanShow?"OK":"FAIL",
        g_fnCanShow?(unsigned long long)(g_fnCanShow-g_gameBase):0);

    // Step 4a: Find vtable start via RTTI Complete Object Locator (vtable[-1])
    // In MSVC x64, vtable[-1] is a pointer to the RTTICompleteObjectLocator.
    // The COL has signature=1 (DWORD at offset 0) and pTypeDescriptor (RVA at offset 12)
    // pointing to a TypeDescriptor whose name starts with ".?AV".
    // Scan backwards from the handler entry to find this boundary.
    if (g_warehouseVtableEntry) {
        for (uintptr_t scan = g_warehouseVtableEntry - 8; scan > g_warehouseVtableEntry - 0x2000; scan -= 8) {
            uintptr_t colPtr = *(uintptr_t*)(scan - 8);  // candidate vtable[-1]
            if (colPtr <= g_gameBase || colPtr >= g_gameBase + g_imageSize - 24) continue;
            // Check RTTI COL signature (must be 1 for x64)
            if (*(uint32_t*)colPtr != 1) continue;
            // Check pTypeDescriptor RVA (offset 12 in COL) points to valid TypeDescriptor
            uint32_t tdRVA = *(uint32_t*)(colPtr + 12);
            uintptr_t tdAddr = g_gameBase + tdRVA;
            if (tdAddr <= g_gameBase || tdAddr >= g_gameBase + g_imageSize - 20) continue;
            // TypeDescriptor: vfptr(8) + spare(8) + name[0..3] = ".?AV"
            const char* tdName = (const char*)(tdAddr + 16);
            if (tdName[0] == '.' && tdName[1] == '?' && tdName[2] == 'A') {
                g_warehouseVtableStart = scan;
                Log("  Vtable start at base+0x%llX (handler offset 0x%llX, class=%.60s)",
                    (unsigned long long)(scan - g_gameBase),
                    (unsigned long long)(g_warehouseVtableEntry - scan), tdName);
                break;
            }
        }
        if (!g_warehouseVtableStart)
            Log("  Vtable start: FAIL (RTTI scan)");
    }

    // Step 4b: Find modal dialog offset in handler struct (update-proof modal detection)
    // Multiple handler functions find ModalMessageView via findChildByName, create a dialog,
    // and store it at handler+N. The store pattern is: MOV [REG+disp32], RAX; TEST RAX, RAX
    // We iterate LEA xrefs to "ModalMessageView" and find the one with this store pattern.
    {
        uintptr_t strMV = FindString("ModalMessageView");
        if (strMV) {
            uintptr_t leaModal = 0;
            uintptr_t searchFrom = g_fnHandler > 0x10000 ? g_fnHandler - 0x10000 : 0;
            while ((leaModal = FindLEA(strMV, searchFrom)) != 0) {
                // Only consider LEAs near the warehouse handler (same class)
                if (g_fnHandler && leaModal > g_fnHandler + 0x10000) break;
                uint8_t* p = (uint8_t*)leaModal;
                for (int i = 0; i < 0xC00; i++) {
                    uint8_t* q = p + i;
                    // Match: REX.W MOV [REG+disp32], RAX
                    if ((q[0] & 0xFE) != 0x48 || q[1] != 0x89) continue;
                    uint8_t modrm = q[2];
                    if ((modrm & 0xF8) != 0x80) continue;  // mod=10, reg=000 (RAX src)
                    int dispOff = 3;
                    if ((modrm & 0x07) == 0x04) dispOff = 4;  // SIB byte present
                    uint32_t disp = *(uint32_t*)(q + dispOff);
                    if (disp < 0x100 || disp >= 0x1000) continue;
                    // Validate: TEST RAX,RAX (48 85 C0) within 16 bytes, then JZ, then MOV [RAX+0x20],REG
                    uint8_t* a = q + dispOff + 4;
                    bool found = false;
                    for (int t = 0; t < 16 && !found; t++) {
                        if (a[t] != 0x48 || a[t+1] != 0x85 || a[t+2] != 0xC0) continue;
                        uint8_t* jz = a + t + 3;
                        int jzLen = 0;
                        if (jz[0] == 0x74) jzLen = 2;
                        else if (jz[0] == 0x0F && jz[1] == 0x84) jzLen = 6;
                        if (!jzLen) continue;
                        uint8_t* bp = jz + jzLen;
                        if ((bp[0] & 0xFC) == 0x48 && bp[1] == 0x89 &&
                            (bp[2] & 0xC7) == 0x40 && bp[3] == 0x20) {
                            found = true;
                        }
                    }
                    // Keep the largest matching offset (warehouse-specific > base class)
                    if (found && disp > g_modalDialogOff) g_modalDialogOff = disp;
                }
                // Continue scanning all LEAs — don't stop at first match
                searchFrom = leaModal + 1;
            }
        }
    }
    Log("ModalDlgOff:  %s offset=0x%X (string-xref → MOV [REG+N])",
        g_modalDialogOff?"OK":"FAIL", g_modalDialogOff);

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
    // QOL: Hides cursor immediately when closing warehouse
    if (g_fnModeSwitcher) {
        uintptr_t targets[32];
        int n = FindAllCALLsAfter(g_fnModeSwitcher, 0x200, targets, 32);
        for (int i = 0; i < n; i++) {
            uint8_t* t = (uint8_t*)targets[i];
            if (t[0] == 0xE9) {
                int32_t rel = *(int32_t*)(t + 1);
                uintptr_t realFn = (uintptr_t)(t + 5) + rel;
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

    // Step 7: Find language byte dynamically
    // The Steam API init function (FUN_140487400) compares Steam's language string
    // against a table of known languages ("koreana", "english", ...) and stores the
    // matching index as a single byte in a global variable.
    // Algorithm: find "koreana" string → find pointer table → find code reference →
    // scan forward for MOV byte [rip+disp32], reg (the write to the global).
    {
        uintptr_t strKoreana = FindString("koreana");
        if (strKoreana) {
            // Find pointer to "koreana" in .rdata (first entry of the language string table)
            uint8_t* base = (uint8_t*)g_gameBase;
            uintptr_t tableAddr = 0;
            for (DWORD i = 0; i + 8 <= g_imageSize; i += 8) {
                if (*(uintptr_t*)(base + i) == strKoreana) {
                    tableAddr = g_gameBase + i;
                    break;
                }
            }
            if (tableAddr) {
                // Find code that loads from this table: [reg + reg*8 + tableDisp]
                // The displacement is tableAddr - gameBase, encoded as 4 LE bytes in the instruction
                uint32_t tableDisp = (uint32_t)(tableAddr - g_gameBase);
                uint8_t* dispBytes = (uint8_t*)&tableDisp;
                uintptr_t codeRef = 0;
                // Scan code section (first ~60% of image) for the 4-byte displacement
                DWORD codeLimit = (DWORD)(g_imageSize * 6 / 10);
                for (DWORD i = 0; i + 4 <= codeLimit; i++) {
                    if (base[i] == dispBytes[0] && base[i+1] == dispBytes[1] &&
                        base[i+2] == dispBytes[2] && base[i+3] == dispBytes[3]) {
                        codeRef = g_gameBase + i + 4;  // right after the displacement
                        break;
                    }
                }
                if (codeRef) {
                    // Scan forward for MOV byte ptr [rip+disp32], reg8
                    // Encoding: (optional REX 40-4F) 88 modrm, where modrm & 0xC7 == 0x05
                    uint8_t* scan = (uint8_t*)codeRef;
                    for (int j = 0; j < 80; j++) {
                        bool hasRex = (scan[j] >= 0x40 && scan[j] <= 0x4F);
                        int opOff = hasRex ? j + 1 : j;
                        if (scan[opOff] == 0x88 && (scan[opOff+1] & 0xC7) == 0x05) {
                            int32_t disp = *(int32_t*)(scan + opOff + 2);
                            uintptr_t addr = (uintptr_t)(scan + opOff + 6) + disp;
                            if (addr > g_gameBase && addr < g_gameBase + g_imageSize) {
                                g_langByteAddr = addr;
                                break;
                            }
                        }
                    }
                }
            }
        }
        Log("LangByte:     %s base+0x%llX (koreana table scan)", g_langByteAddr?"OK":"FAIL",
            g_langByteAddr?(unsigned long long)(g_langByteAddr-g_gameBase):0);
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

    Log("=== Private Storage Anywhere v1.2.5 ===");
    {char cls[256]={};char ttl[256]={};GetClassNameA(g_gameWindow,cls,256);GetWindowTextA(g_gameWindow,ttl,256);
    Log("Game window: class='%s' title='%s'",cls,ttl);}
    g_gameBase=(uintptr_t)GetModuleHandleA("CrimsonDesert.exe");
    if(!g_gameBase){Log("FATAL: no game base");return 0;}
    MODULEINFO mi;GetModuleInformation(GetCurrentProcess(),(HMODULE)g_gameBase,&mi,sizeof(mi));
    g_imageSize=mi.SizeOfImage;
    Log("Base: 0x%llX  Size: 0x%X  Hotkey: 0x%02X",
        (unsigned long long)g_gameBase, g_imageSize, g_hotkey);

    // Hash meta/0.papgt to detect modded game files (JSON mods etc.)
    {
        std::string metaPath(dp);
        size_t bs = metaPath.rfind('\\');
        if (bs != std::string::npos) {
            metaPath = metaPath.substr(0, bs);           // strip filename
            bs = metaPath.rfind('\\');
            if (bs != std::string::npos)
                metaPath = metaPath.substr(0, bs);       // strip bin64
        }
        metaPath += "\\meta\\0.papgt";
        uint32_t crc = FileCRC32(metaPath.c_str());
        if (crc) Log("meta/0.papgt CRC32: %08X", crc);
        else     Log("meta/0.papgt: NOT FOUND");
    }

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

    if(!IsWindow(g_gameWindow)){
        g_gameWindow=FindGameWindow();
        if(!g_gameWindow||!IsWindow(g_gameWindow)){Log("FATAL: game window invalid before WndProc hook");return 0;}
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
