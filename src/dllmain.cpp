#include <windows.h>
#include <psapi.h>
#include <cstdio>
#include <cstring>
#include <string>

// ============================================================
//  Private Storage Anywhere
//
//  Opens the Camp Warehouse (Private Storage) and the 5 housing
//  chests (Gatherables, Dresser, Refrigerator, Symbol, Collecting)
//  from anywhere with a hotkey (defaults F4–F9) or controller
//  button (default LB + LeftStick for Private, LB + RightStick for
//  Gatherables).
//
//  See CHANGELOG.txt for version history.
// ============================================================

static uintptr_t g_gameBase = 0, g_imageSize = 0;
static bool g_ready = false;
static FILE* g_logFile = nullptr;
static HMODULE g_hModule = nullptr;
static HWND g_gameWindow = nullptr;
static WNDPROC g_originalWndProc = nullptr;
static bool g_enabled = true, g_debugLog = true;
// Legacy "single hotkey" global. Kept for backwards compatibility with old
// INIs that used `Hotkey=...` instead of per-panel <Name>Hotkey keys.
// LoadConfig() overrides this with the INI value (default 0 = disabled).
// The runtime initial value here is also 0 so that no key fires before
// LoadConfig has run.
static DWORD g_hotkey = 0;
static DWORD g_modifierKey = 0;
static DWORD g_reloadKey = 0;
static char g_iniPath[MAX_PATH] = {};

// Resolved function addresses
static uintptr_t g_fnHandler = 0;
static uintptr_t g_fnModeSwitcher = 0, g_fnCanShow = 0, g_fnSetInventory = 0;
static uintptr_t g_fnSetTitle = 0;
static uintptr_t g_warehouseVtableEntry = 0;  // vtable address containing handler — used for auto-capture verification
static uintptr_t g_warehouseVtableStart = 0;  // vtable start of warehouse class — set on first successful capture
static uintptr_t g_langByteAddr = 0;      // address of language byte (resolved dynamically from Steam API init function)

// Dialog open events. The openers of the "View Details" popup and of the
// quantity dialog are found via the "ItemDetailModalMessage" /
// "CountingModalMessage" string xrefs and hooked read-only; each open resets
// the modal state machine (g_modalDismissed, see IsNewModalDialogVisible).
// g_itemDetailActiveCount is the fallback flag, used only while the game's
// modal-layer test (IsViewOpen("ModalMessageView")) is unavailable.
static volatile LONG g_itemDetailActiveCount = 0;
static uintptr_t g_addrItemDetailCtor = 0;
static uintptr_t g_addrCountingModal  = 0;   // "CountingModalMessage" opener (quantity dialog)

// Struct offsets. Everything below is resolved from the game code at startup;
// the initial values are only the layout of the build each one was first seen
// on and must never be used directly. A resolver that fails leaves the feature
// disabled rather than writing through a stale offset.
static uint32_t g_offActiveFlag   = 0x118;  // handler+N: u8 active flag, read by CanShow (2.01.00: 0x130)
static uint32_t g_offPanelValue   = 0x110;  // handler+N: panel value; moves with the active flag (2.01.00: 0x128)
static uint32_t g_offBottomLabel  = 0x308;  // handler+N: lower inventory label node (2.01.00: 0x3E0)
static uint32_t g_offTopTitle     = 0x0E8;  // handler+N: top title node, from the
                                            // "selector-title-subtext-stage" binding (2.01.00: 0xF0);
                                            // 0 = write disabled (chain could not be cross-validated)
static uint32_t g_offDonationState = 0x330; // handler+N: first of 3 donation faction shorts (cleared on open)
static uintptr_t g_fnSetDonationFaction = 0; // "SetDonationFaction" command handler, scanned for the offset above
// Sub-objects the handler's 0x15 ("prepare") command makes three virtual calls
// on. All three must be non-null before an empty 0x15 is sent, otherwise the
// dispatcher crashes (they are only initialised after an NPC interaction).
// Resolved from the Handler body: three consecutive
// `MOV RCX,[param_1+disp32]; MOV RAX,[RCX]; CALL [RAX+imm]` (2.01.00: 0x3A0/0x3B0/0x3D8).
static uint32_t g_offPrepare1 = 0x2c8;
static uint32_t g_offPrepare2 = 0x2d8;
static uint32_t g_offPrepare3 = 0x300;
// Game-manager singleton slot; mainChar = *(*(slot) + 0x48). Resolved as the
// global that is by far most often loaded and then dereferenced at +0x48
// (2.01.00: base+0x6C29C70, 247 sites vs 22 for the runner-up). mainChar only
// serves as a "session is loaded" gate and as the neighbourhood for the
// session-global fallback scan in ResolveInvContainer().
static uintptr_t g_mainCharGlobalPtr = 0;

// ---- CD 2.01.00 menu-request API -------------------------------------------
// The mode/sub-mode cluster left mainChar in 2.01.00, which killed the old
// "write the flag bytes and let the tick derive the view tags" approach. The
// replacement is the game's own request queue:
//
//     MenuRequest(menuObj, screenId, open)
//
// It allocates a small request record, stores screenId at +8 and the open flag
// at +9, and pushes it onto the queue at menuObj+0x68. Call sites prove the
// signature: the same screenId appears once with open=1 and once with open=0
// (screen 3 and screen 7 both do). The warehouse needs the screen whose
// ModeSwitcher case emits the "store" view tag — WareHouseView is declared in
// uigameconfig2.xml as tag2="store ingamemenu", so that tag is what mounts it.
static uintptr_t g_menuRequestFn  = 0;
// Game-menu gate (replaces the mainChar mode/sub-mode check that 2.01.00 took
// away): the game's own per-view open test. FindPanelTop(pm, name) returns the
// view object; its state byte at +g_panelStateOff reads (st & 0x60) == 0x40
// while the view is open. pm (the panel manager) is captured from FindPanelTop's
// first argument by a read-only hook and validated against the array it walks.
static uintptr_t g_fnFindPanelTop  = 0;
static uint32_t  g_panelStateOff   = 0;
static uint32_t  g_pmArrayOff      = 0;    // pm+N: panel entry array (from FindPanelTop's prolog)
static uint32_t  g_pmCountOff      = 0;    // pm+N: panel entry count
static volatile LONG64 g_panelManager = 0;
static uintptr_t g_menuRootGlobal = 0;   // menuObj = *( *(global) + g_menuObjOff )
static uint32_t  g_menuObjOff     = 0;
static int32_t   g_storeScreenId  = -1;  // derived from ModeSwitcher; -1 = unknown
static int32_t   g_storeScreenIdIni = -1; // INI override, -1 = use the derived value

// Captured game state (accessed from multiple threads via Interlocked ops)
static volatile LONG64 g_mainChar = 0;
// Single handler slot. All six storages use the same UIGamePlayControlRootWarehouse2
// controller; they differ only in the SetInventory filter string passed on open.
static volatile LONG64 g_handlerThis = 0;
// Original content of handler+g_offPanelValue, captured at the first open and
// restored on close. -1 = not yet captured.
static volatile LONG64 g_savedPanelValueSlot = -1;
// false once the captured PanelValue slot holds a canonical pointer instead of a
// small type-id scalar — i.e. handler+g_offPanelValue has drifted to a different
// field. Then the override/restore writes are skipped so we never clobber a live
// pointer with a valid-but-wrong write (which SEH cannot catch).
static bool g_panelValueSlotValid = true;
static volatile LONG g_warehouseActive = 0;
static volatile LONG g_handlerHitCount = 0;

// Active panel selector. Every hotkey opens its own panel from cold; pressing
// any panel hotkey while the warehouse is open closes it.
enum ActivePanel {
    PANEL_PRIVATE      = 0,  // CampWareHouse (Private Storage, capacity never touched)
    PANEL_GATHERABLES  = 1,  // Housing_GatheredMaterials (Gatherables Chest)
    PANEL_DRESSER      = 2,  // Housing_Dresser
    PANEL_REFRIGERATOR = 3,  // Housing_Refrigerator
    PANEL_SYMBOL       = 4,  // Housing_Symbol
    PANEL_COLLECTING   = 5,  // Housing_Collecting
    PANEL_COUNT        = 6,
};
static volatile LONG g_activePanel = PANEL_PRIVATE;

// Per-panel definition. initString feeds SetInventory; hotkey is the direct-
// open shortcut (0 = disabled). Each hotkey is a panel toggle: opens cold if
// warehouse is closed, otherwise closes the warehouse.
struct PanelDef {
    const char* name;                // English logging name
    char        initString[256];     // SetInventory filter (overridable via INI)
    DWORD       hotkey;              // Keyboard VK code, 0 = no dedicated hotkey
    DWORD       modifier;            // Keyboard VK code, 0 = no modifier
    WORD        controllerButton;    // XInput button mask, 0 = no button
    WORD        controllerModifier;  // XInput hold-this-first mask, 0 = no modifier
    int         psButtonByteOff;     // PS5/PS4 HID: byte offset from buttons1; -1 = unbound
    BYTE        psButtonBitMask;     // PS5/PS4 HID: bit mask within that byte
    int         psModifierByteOff;   // PS5/PS4 HID modifier byte offset; -1 = no modifier
    BYTE        psModifierBitMask;   // PS5/PS4 HID modifier bit mask
};
// Code defaults match the shipped INI defaults. Fields per row:
//   name, initString, hotkey, modifier, xiButton, xiModifier,
//   psButtonByteOff, psButtonBitMask, psModifierByteOff, psModifierBitMask
// Keyboard defaults: F4..F9 (one per panel). Controller defaults: only
// Private + Gatherables get controller bindings; the other housing chests
// are keyboard-only (rows of 0/-1). PS5/PS4 mirrors the controller layout:
// L1+L3 → Private, L1+R3 → Gatherables.
static PanelDef g_panels[PANEL_COUNT] = {
    { "Private",      "Character,Focus,True;CampWareHouse,Focus,True",              0x73 /*F4*/,  0, 0x0040 /*LStick*/, 0x0100 /*LB*/, 1, 0x40 /*L3*/, 1, 0x01 /*L1*/ },
    { "Gatherables",  "Character,Focus,True;Housing_GatheredMaterials,Focus,True",  0x74 /*F5*/,  0, 0x0080 /*RStick*/, 0x0100 /*LB*/, 1, 0x80 /*R3*/, 1, 0x01 /*L1*/ },
    { "Dresser",      "Character,Focus,True;Housing_Dresser,Focus,True",            0x75 /*F6*/,  0, 0, 0, -1, 0, -1, 0 },
    { "Refrigerator", "Character,Focus,True;Housing_Refrigerator,Focus,True",       0x76 /*F7*/,  0, 0, 0, -1, 0, -1, 0 },
    { "Symbol",       "Character,Focus,True;Housing_Symbol,Focus,True",             0x77 /*F8*/,  0, 0, 0, -1, 0, -1, 0 },
    { "Collecting",   "Character,Focus,True;Housing_Collecting,Focus,True",         0x78 /*F9*/,  0, 0, 0, -1, 0, -1, 0 },
};
// Per-panel last/current state for PS button edge detection (parallel to g_panels[]).
static bool g_panelPsLastDown[PANEL_COUNT] = {};
static bool g_panelPsCurrentDown[PANEL_COUNT] = {};
static bool g_panelPsModifierDown[PANEL_COUNT] = {};
// Per-panel last-down state for XInput button edge detection (parallel to g_panels[]).
// Keeps the XInput per-panel logic structurally identical to the DirectInput version
// (which uses g_panelPsLastDown) — each panel tracks its own rising edge instead of
// sharing the global g_prevButtons mask. This avoids cross-panel interference and
// makes the two paths trivially auditable.
static bool g_panelXiLastDown[PANEL_COUNT] = {};
// XInput B-button last-down state (parallel to g_circleWasDown for DualSense Circle).
static bool g_xiBWasDown = false;

// PanelValue written to handler+g_offPanelValue on every open. The game parses
// it from a sub-command of its own 0x0E show packet; the mod's packet has none,
// so the value is written by hand. All six storages open correctly with the
// shipped defaults (Private 0x276, everything else 0x2D1) — the per-chest INI
// keys exist only as an override should a future build change the value space.
static volatile LONG g_panelValueCfg[PANEL_COUNT] = {};
static volatile LONG g_privatePanelValueCfg     = 0;       // 0 = no override
static volatile LONG g_gatherablesPanelValueCfg = 0;       // 0 = no override

// Which panel's SetInventory channels are currently subscribed. Subscriptions
// accumulate on the controller until an explicit ",False" unbind, so the next
// open must unbind this panel first or the previous chest's items stay visible.
static volatile LONG g_currentBoundPanel = -1;

// Debug key (INI InvDumpKey, default F10): writes the live inventory groups to
// the log. Read-only; that output is what pins a wrong capacity to its cause.
static DWORD g_invDumpKey = 0x79;  // VK_F10

// Set by the hotkey handler right before posting WM_TRIGGER_WAREHOUSE. The Open path
// in TriggerWarehouse reads this and sets g_activePanel accordingly, then resets it.
static volatile LONG g_nextOpenPanel = PANEL_PRIVATE;

static volatile ULONGLONG g_closeTimestamp = 0;  // GetTickCount64 at last close (re-open cooldown)

// Forward declaration (defined later in Utilities section)
static void Log(const char* fmt, ...);
static void InitWarehousePanel(uintptr_t handler, const char* initString);
static bool TriggerWarehouseViewMount(void);
static void TriggerWarehouseViewUnmount(void);
static void LogModalState(const char* prefix);
static bool IsViewOpen(const char* name, uint8_t* stOut);

// Pending-close flags. Set on press while warehouse is active, cleared on
// release-driven close OR on warehouse close from any other path. Defined
// here (instead of next to the input handlers) so TriggerWarehouse's
// close branch can reset them without a forward declaration.
static volatile LONG g_pendingCircleClose = 0;  // PS5/PS4 Circle (HID)
static volatile LONG g_pendingBClose      = 0;  // XInput B

// DLL hot-reload signal. Worker threads (InputThread, slot-capacity worker)
// poll this and exit the loop when set. On normal process exit the OS
// terminates threads before DllMain runs so this is irrelevant; on
// FreeLibrary hot-reload the flag gives workers a chance to bail before
// the image is unmapped under them.
static volatile LONG g_shutdown = 0;

// GetInitStringForActive: returns the SetInventory filter string for the currently active panel.
static inline const char* GetInitStringForActive() {
    LONG i = InterlockedCompareExchange(&g_activePanel, 0, 0);
    if (i < 0 || i >= PANEL_COUNT) i = PANEL_PRIVATE;
    return g_panels[i].initString;
}

// Hook cleanup: every InstallHook/InstallCanShowHook adds itself to this
// table on success, and DLL_PROCESS_DETACH iterates it to restore every
// patched site so a DLL unload (hot-reload of the ASI) leaves the game in
// a clean state — no stale JMP into freed trampoline memory.
struct HookEntry {
    uintptr_t addr;
    int       size;
    uint8_t   orig[28];
};
static HookEntry g_hookTable[16] = {};
static int       g_hookCount    = 0;



#define WM_TRIGGER_WAREHOUSE (WM_USER + 602)
#define WM_INIT_WAREHOUSE    (WM_USER + 603)
static volatile LONG g_initPending = 0;     // 1 = InputThread should post WM_INIT_WAREHOUSE
static volatile LONG g_initRetryCount = 0;  // retry counter for deferred warehouse init

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

// PSButton bindings are now per-panel (see PanelDef::psButtonByteOff/Mask).
// Edge state arrays live next to g_panels[].

static bool g_circleWasDown = false;

// Cached device identification (so we only call GetRawInputDeviceInfo once per handle)
static HANDLE g_cachedHidDevice = nullptr;
static bool   g_cachedIsSony = false;
static int    g_cachedReportOffset = -1;  // offset to buttons1 byte (-1 = unknown)

// Parsed button state from last WM_INPUT
static bool g_lastCircle   = false;

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
}

// Parses Circle + per-panel PSButton/PSModifier state from WM_INPUT HID
// report. Stores results in g_lastCircle, g_panelPsCurrentDown[],
// g_panelPsModifierDown[].
static void ParseSonyButtons(LPARAM lParam) {
    g_lastCircle = false;
    for (int i = 0; i < PANEL_COUNT; i++) {
        g_panelPsCurrentDown[i] = false;
        g_panelPsModifierDown[i] = false;
    }

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

    // Circle is always at buttons1 (offset + 0) — used for close-on-release
    g_lastCircle = (report[offset] & CIRCLE_BIT) != 0;

    // Per-panel PSButton + PSModifier state. Each panel that has a binding
    // gets its current pressed state populated; panels without binding stay
    // false (and an unset modifier counts as "no modifier required" later).
    for (int i = 0; i < PANEL_COUNT; i++) {
        if (g_panels[i].psButtonByteOff >= 0) {
            int psOff = offset + g_panels[i].psButtonByteOff;
            if ((DWORD)psOff < reportLen)
                g_panelPsCurrentDown[i] = (report[psOff] & g_panels[i].psButtonBitMask) != 0;
        }
        if (g_panels[i].psModifierByteOff >= 0) {
            int modOff = offset + g_panels[i].psModifierByteOff;
            if ((DWORD)modOff < reportLen)
                g_panelPsModifierDown[i] = (report[modOff] & g_panels[i].psModifierBitMask) != 0;
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

static const char* GetPrivateStorageTitle() {
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

static const char* GetGatherablesTitle() {
    // EN confirmed via in-game NPC visit: "Gatherables Chest". Other languages
    // are best-effort guesses — confirm at NPC chest in each language and
    // update strings if needed.
    switch (GetGameLanguage()) {
        case  0: return "\xEC\x88\x98\xEC\xA7\x91 \xEC\x83\x81\xEC\x9E\x90";              // KR: 수집 상자
        case  1: return "Gatherables Chest";                                                // EN (confirmed)
        case  2: return "\xE6\x8E\xA1\xE9\x9B\x86\xE7\x89\xA9\xE3\x83\x81\xE3\x82\xA7\xE3\x82\xB9\xE3\x83\x88"; // JP: 採集物チェスト
        case  3: return "\xD0\xA1\xD1\x83\xD0\xBD\xD0\xB4\xD1\x83\xD0\xBA \xD1\x81\xD0\xB1\xD0\xBE\xD1\x80\xD0\xB0";  // RU: Сундук сбора
        case  4: return "Toplama Sand\xC4\xB1\xC4\x9F\xC4\xB1";                            // TR
        case  5: return "Cofre de Recolecci\xC3\xB3n";                                      // ES
        case  6: return "Cofre de Recolecci\xC3\xB3n";                                      // MX
        case  7: return "Coffre de R\xC3\xA9" "colte";                                     // FR
        case  8: return "Sammeltruhe";                                                      // DE
        case  9: return "Baule da Raccolta";                                                // IT
        case 10: return "Skrzynia Zbiorcza";                                                // PL
        case 11: return "Ba\xC3\xBA de Coleta";                                            // BR
        case 12: return "\xE6\x8E\xA1\xE9\x9B\x86\xE5\xAE\x9D\xE7\xAE\xB1";                // TW
        case 13: return "\xE9\x87\x87\xE9\x9B\x86\xE5\xAE\x9D\xE7\xAE\xB1";                // CN
        default: return "Gatherables Chest";
    }
}

// Per-language titles for the additional housing panels.
// NOTE: these are best-effort translations — these housing chests
// have no in-game UI key (only the internal channel name "Housing_*"
// which the player never sees), so the mod must supply its own text
// rather than calling the game's localizer.  If any translation feels
// off in a specific language, override via the INI (future work) or
// edit the string here. Encoding rule: plain "" with \x hex escapes
// (NOT u8"") — MSVC /utf-8 + u8"" double-encodes bytes > 0x7F.
static const char* GetDresserTitle() {
    switch (GetGameLanguage()) {
        case  0: return "\xEC\x84\x9C\xEB\x9E\x8D\xEC\x9E\xA5";                                    // KR: 서랍장
        case  1: return "Dresser";                                                                    // EN
        case  2: return "\xE5\x8C\x96\xE7\xB2\xA7\xE5\x8F\xB0";                                    // JP: 化粧台
        case  3: return "\xD0\x9A\xD0\xBE\xD0\xBC\xD0\xBE\xD0\xB4";                                // RU: Комод
        case  4: return "\xC5\x9Eifonyer";                                                            // TR: Şifonyer
        case  5: return "Tocador";                                                                    // ES
        case  6: return "Tocador";                                                                    // MX
        case  7: return "Commode";                                                                    // FR
        case  8: return "Kommode";                                                                    // DE
        case  9: return "Cassettone";                                                                 // IT
        case 10: return "Komoda";                                                                     // PL
        case 11: return "C\xC3\xB4moda";                                                             // BR: Cômoda
        case 12: return "\xE6\x8A\xBD\xE5\xB1\x89\xE6\xAB\x83";                                    // TW: 抽屜櫃
        case 13: return "\xE6\x8A\xBD\xE5\xB1\x89\xE6\x9F\x9C";                                    // CN: 抽屉柜
        default: return "Dresser";
    }
}
static const char* GetRefrigeratorTitle() {
    switch (GetGameLanguage()) {
        case  0: return "\xEB\x83\x89\xEC\x9E\xA5\xEA\xB3\xA0";                                    // KR: 냉장고
        case  1: return "Refrigerator";                                                               // EN
        case  2: return "\xE5\x86\xB7\xE8\x94\xB5\xE5\xBA\xAB";                                    // JP: 冷蔵庫
        case  3: return "\xD0\xA5\xD0\xBE\xD0\xBB\xD0\xBE\xD0\xB4\xD0\xB8\xD0\xBB\xD1\x8C\xD0\xBD\xD0\xB8\xD0\xBA"; // RU: Холодильник
        case  4: return "Buzdolab\xC4\xB1";                                                          // TR: Buzdolabı
        case  5: return "Frigor\xC3\xAD" "fico";                                                    // ES: Frigorífico
        case  6: return "Refrigerador";                                                               // MX
        case  7: return "R\xC3\xA9" "frig\xC3\xA9rateur";                                          // FR: Réfrigérateur
        case  8: return "K\xC3\xBChlschrank";                                                        // DE: Kühlschrank
        case  9: return "Frigorifero";                                                                // IT
        case 10: return "Lod\xC3\xB3wka";                                                            // PL: Lodówka
        case 11: return "Geladeira";                                                                  // BR
        case 12: return "\xE5\x86\xB0\xE7\xAE\xB1";                                                  // TW: 冰箱
        case 13: return "\xE5\x86\xB0\xE7\xAE\xB1";                                                  // CN: 冰箱
        default: return "Refrigerator";
    }
}
static const char* GetSymbolTitle() {
    switch (GetGameLanguage()) {
        case  0: return "\xEC\x8B\xAC\xEB\xB3\xBC \xEC\xB0\xBD\xEA\xB3\xA0";                       // KR: 심볼 창고
        case  1: return "Symbol Storage";                                                             // EN
        case  2: return "\xE3\x82\xB7\xE3\x83\xB3\xE3\x83\x9C\xE3\x83\xAB\xE5\x80\x89\xE5\xBA\xAB"; // JP: シンボル倉庫
        case  3: return "\xD0\xA1\xD0\xBA\xD0\xBB\xD0\xB0\xD0\xB4 \xD1\x81\xD0\xB8\xD0\xBC\xD0\xB2\xD0\xBE\xD0\xBB\xD0\xBE\xD0\xB2"; // RU: Склад символов
        case  4: return "Sembol Deposu";                                                              // TR
        case  5: return "Almac\xC3\xA9n de S\xC3\xAD" "mbolos";                                    // ES: Almacén de Símbolos
        case  6: return "Almac\xC3\xA9n de S\xC3\xAD" "mbolos";                                    // MX
        case  7: return "Stockage de Symboles";                                                       // FR
        case  8: return "Symbol-Lager";                                                               // DE
        case  9: return "Deposito Simboli";                                                           // IT
        case 10: return "Magazyn Symboli";                                                            // PL
        case 11: return "Armaz\xC3\xA9m de S\xC3\xAD" "mbolos";                                    // BR
        case 12: return "\xE7\xAC\xA6\xE8\x99\x9F\xE5\x80\x89\xE5\xBA\xAB";                        // TW: 符號倉庫
        case 13: return "\xE7\xAC\xA6\xE5\x8F\xB7\xE4\xBB\x93\xE5\xBA\x93";                        // CN: 符号仓库
        default: return "Symbol Storage";
    }
}
static const char* GetCollectingTitle() {
    switch (GetGameLanguage()) {
        case  0: return "\xEC\x88\x98\xEC\xA7\x91 \xEC\xB0\xBD\xEA\xB3\xA0";                       // KR: 수집 창고
        case  1: return "Collecting Storage";                                                         // EN
        case  2: return "\xE3\x82\xB3\xE3\x83\xAC\xE3\x82\xAF\xE3\x82\xB7\xE3\x83\xA7\xE3\x83\xB3\xE5\x80\x89\xE5\xBA\xAB"; // JP: コレクション倉庫
        case  3: return "\xD0\xA1\xD0\xBA\xD0\xBB\xD0\xB0\xD0\xB4 \xD0\xBA\xD0\xBE\xD0\xBB\xD0\xBB\xD0\xB5\xD0\xBA\xD1\x86\xD0\xB8\xD0\xB9"; // RU: Склад коллекций
        case  4: return "Koleksiyon Deposu";                                                          // TR
        case  5: return "Almac\xC3\xA9n de Colecci\xC3\xB3n";                                       // ES: Almacén de Colección
        case  6: return "Almac\xC3\xA9n de Colecci\xC3\xB3n";                                       // MX
        case  7: return "Stockage de Collection";                                                     // FR
        case  8: return "Sammlungs-Lager";                                                            // DE
        case  9: return "Deposito Collezione";                                                        // IT
        case 10: return "Magazyn Kolekcji";                                                           // PL
        case 11: return "Armaz\xC3\xA9m de Cole\xC3\xA7\xC3\xA3o";                                  // BR: Armazém de Coleção
        case 12: return "\xE6\x94\xB6\xE8\x97\x8F\xE5\x80\x89\xE5\xBA\xAB";                        // TW: 收藏倉庫
        case 13: return "\xE6\x94\xB6\xE8\x97\x8F\xE4\xBB\x93\xE5\xBA\x93";                        // CN: 收藏仓库
        default: return "Collecting Storage";
    }
}

static const char* GetWarehouseTitle() {
    LONG i = InterlockedCompareExchange(&g_activePanel, 0, 0);
    switch (i) {
        case PANEL_PRIVATE:      return GetPrivateStorageTitle();
        case PANEL_GATHERABLES:  return GetGatherablesTitle();
        case PANEL_DRESSER:      return GetDresserTitle();
        case PANEL_REFRIGERATOR: return GetRefrigeratorTitle();
        case PANEL_SYMBOL:       return GetSymbolTitle();
        case PANEL_COLLECTING:   return GetCollectingTitle();
        default:                 return GetPrivateStorageTitle();
    }
}

// Is a modal dialog (quantity / confirm / "View Details") up over the
// warehouse? The warehouse code itself asks the panel manager for
// "ModalMessageView" (uigameconfig.xml: the modal layer, layer 100) and reads
// its view state — so do we; the ItemDetailOpen hook flag is the fallback
// while that test is unavailable (panel manager not captured yet).
//
// Modal state machine. The layer object (ModalMessageView) reports "open" from
// the moment a dialog opens until a few seconds after it was dismissed — its
// first 0x100 bytes are byte-identical with the dialog open, just dismissed
// and seconds later (2.02 dump), so it carries no "dialog gone" field. The
// dialog state is therefore tracked by events:
//   open      -> the game's own dialog openers (ItemDetailModalMessage and
//                CountingModalMessage hooks) clear g_modalDismissed
//   dismissed -> an ESC / B / Circle press passed on to the game sets
//                g_modalDismissed (the game dismisses the dialog with it)
//   closed    -> the layer reading "closed" clears g_modalDismissed
// A dialog is up when the layer is open and no dismissing press has been
// passed on since the last open event. No timers.
static volatile LONG g_modalDismissed = 0;

static bool IsNewModalDialogVisible() {
    if (g_fnFindPanelTop && g_panelStateOff &&
        InterlockedCompareExchange64(&g_panelManager, 0, 0)) {
        if (!IsViewOpen("ModalMessageView", nullptr)) {
            InterlockedExchange(&g_modalDismissed, 0);
            return false;
        }
        return InterlockedCompareExchange(&g_modalDismissed, 0, 0) == 0;
    }
    return InterlockedCompareExchange(&g_itemDetailActiveCount, 0, 0) > 0;
}

static DWORD ReadHexValue(const char* section, const char* key, DWORD defaultVal, const char* iniPath) {
    char buf[32];
    GetPrivateProfileStringA(section, key, "", buf, sizeof(buf), iniPath);
    if (buf[0] == '\0') return defaultVal;
    return (DWORD)strtoul(buf, nullptr, 16);
}

// Map a PSButton name string to (byte offset from buttons1, bit mask).
// Returns false for "none" or unknown names. Used both for the legacy
// global PSButton key and for per-panel <Name>PSButton overrides.
static bool ParsePSButtonName(const char* name, int* outOff, BYTE* outMask) {
    if (!name || !name[0] || _stricmp(name, "none") == 0) return false;
    struct Map { const char* n; int off; BYTE mask; };
    static const Map kMap[] = {
        { "Share",    1, 0x10 }, { "Options",  1, 0x20 },
        { "Circle",   0, 0x40 }, { "Triangle", 0, 0x80 },
        { "Square",   0, 0x10 }, { "Cross",    0, 0x20 },
        { "L1",       1, 0x01 }, { "R1",       1, 0x02 },
        { "L3",       1, 0x40 }, { "R3",       1, 0x80 },
        { "Touchpad", 2, 0x02 }, { "PS",       2, 0x01 }, { "Mute", 2, 0x04 },
    };
    for (const auto& m : kMap) {
        if (_stricmp(name, m.n) == 0) { *outOff = m.off; *outMask = m.mask; return true; }
    }
    return false;
}

static void LoadConfig(const char* p) {
    g_enabled = GetPrivateProfileIntA("Settings","Enabled",1,p)!=0;
    g_debugLog = GetPrivateProfileIntA("Settings","DebugLog",0,p)!=0;
    // Legacy "Hotkey" (single Private toggle). Default 0 = disabled. The
    // new per-panel layout uses PrivateHotkey=… for control. Keeping any
    // non-zero legacy default would silently steal whatever that key is
    // now assigned to in the per-panel layout (e.g. PrivateHotkey=F4).
    g_hotkey = ReadHexValue("Settings", "Hotkey", 0, p);
    g_modifierKey = ReadHexValue("Settings", "ModifierKey", 0, p);
    g_controllerButton = (WORD)ReadHexValue("Settings", "ControllerButton", 0, p);
    g_controllerModifier = (WORD)ReadHexValue("Settings", "ControllerModifier", 0, p);
    g_reloadKey = ReadHexValue("Settings", "ReloadKey", 0, p);

    // Manual override for the warehouse screen id. -1 (default) uses the value
    // derived from ModeSwitcher. Only touch this if the boot log shows the
    // derivation failed or the wrong screen opens.
    g_storeScreenIdIni = GetPrivateProfileIntA("Settings", "StoreScreenId", -1, p);

    g_invDumpKey = ReadHexValue("Settings", "InvDumpKey", 0x79, p);

    InterlockedExchange(&g_privatePanelValueCfg,
        (LONG)ReadHexValue("Settings", "PrivatePanelValue",     0,      p));
    InterlockedExchange(&g_gatherablesPanelValueCfg,
        (LONG)ReadHexValue("Settings", "GatherablesPanelValue", 0x02D1, p));

    // Per-panel INI keys: <Name>Hotkey, <Name>Modifier, <Name>ControllerButton,
    // <Name>ControllerModifier (plus optional <Name>InitString override).
    // Defaults come from the g_panels[] static initializer.
    //
    // Private's controller config is also seeded from the legacy
    // ControllerButton/ControllerModifier keys above so existing user INIs
    // keep working without changes.
    g_panels[PANEL_PRIVATE].controllerButton   = g_controllerButton;
    g_panels[PANEL_PRIVATE].controllerModifier = g_controllerModifier;

    static const char* kIniKey[PANEL_COUNT] = {
        "Private", "Gatherables", "Dresser", "Refrigerator", "Symbol", "Collecting"
    };
    for (int i = 0; i < PANEL_COUNT; i++) {
        {
            char kv[64];
            snprintf(kv, sizeof(kv), "%sPanelValue", kIniKey[i]);
            InterlockedExchange(&g_panelValueCfg[i],
                (LONG)ReadHexValue("Settings", kv, 0, p));
        }
        char keyName[64];
        snprintf(keyName, sizeof(keyName), "%sHotkey", kIniKey[i]);
        g_panels[i].hotkey = ReadHexValue("Settings", keyName, g_panels[i].hotkey, p);
        snprintf(keyName, sizeof(keyName), "%sModifier", kIniKey[i]);
        g_panels[i].modifier = ReadHexValue("Settings", keyName, g_panels[i].modifier, p);
        snprintf(keyName, sizeof(keyName), "%sControllerButton", kIniKey[i]);
        g_panels[i].controllerButton = (WORD)ReadHexValue("Settings", keyName, g_panels[i].controllerButton, p);
        snprintf(keyName, sizeof(keyName), "%sControllerModifier", kIniKey[i]);
        g_panels[i].controllerModifier = (WORD)ReadHexValue("Settings", keyName, g_panels[i].controllerModifier, p);
        snprintf(keyName, sizeof(keyName), "%sInitString", kIniKey[i]);
        char buf[256] = {};
        GetPrivateProfileStringA("Settings", keyName, g_panels[i].initString,
                                 buf, sizeof(buf), p);
        if (buf[0]) strncpy(g_panels[i].initString, buf, sizeof(g_panels[i].initString) - 1);
    }

    // PSButton + PSModifier (legacy globals) → seed Private's panel slot.
    // Existing user INIs with PSButton=Share keep working.
    char psBtn[32];
    GetPrivateProfileStringA("Settings", "PSButton", "none", psBtn, sizeof(psBtn), p);
    int legacyOff; BYTE legacyMask;
    if (ParsePSButtonName(psBtn, &legacyOff, &legacyMask)) {
        g_panels[PANEL_PRIVATE].psButtonByteOff = legacyOff;
        g_panels[PANEL_PRIVATE].psButtonBitMask = legacyMask;
    }
    char psMod[32];
    GetPrivateProfileStringA("Settings", "PSModifier", "none", psMod, sizeof(psMod), p);
    if (ParsePSButtonName(psMod, &legacyOff, &legacyMask)) {
        g_panels[PANEL_PRIVATE].psModifierByteOff = legacyOff;
        g_panels[PANEL_PRIVATE].psModifierBitMask = legacyMask;
    }

    // Per-panel <Name>PSButton + <Name>PSModifier overrides. Both use the
    // same button-name strings (Share, Circle, Cross, L1, R1, ...).
    for (int i = 0; i < PANEL_COUNT; i++) {
        char keyName[64];
        char buf[32] = {};
        snprintf(keyName, sizeof(keyName), "%sPSButton", kIniKey[i]);
        GetPrivateProfileStringA("Settings", keyName, "", buf, sizeof(buf), p);
        if (buf[0]) {
            int off; BYTE mask;
            if (ParsePSButtonName(buf, &off, &mask)) {
                g_panels[i].psButtonByteOff = off;
                g_panels[i].psButtonBitMask = mask;
            } else {
                g_panels[i].psButtonByteOff = -1;
                g_panels[i].psButtonBitMask = 0;
            }
        }

        snprintf(keyName, sizeof(keyName), "%sPSModifier", kIniKey[i]);
        buf[0] = '\0';
        GetPrivateProfileStringA("Settings", keyName, "", buf, sizeof(buf), p);
        if (buf[0]) {
            int off; BYTE mask;
            if (ParsePSButtonName(buf, &off, &mask)) {
                g_panels[i].psModifierByteOff = off;
                g_panels[i].psModifierBitMask = mask;
            } else {
                g_panels[i].psModifierByteOff = -1;
                g_panels[i].psModifierBitMask = 0;
            }
        }
    }
}

// String-Xref helpers (from QuickMenuHotkeys)
// First occurrence of the NUL-terminated string that also STARTS a string
// (preceded by a NUL). A tail match ("QuestMenuPanel" inside
// "DailyQuestMenuPanel") has no code reference of its own.
static uintptr_t FindString(const char* str) {
    uint8_t* base = (uint8_t*)g_gameBase;
    int len = (int)strlen(str);
    for (DWORD i = 0; i + len + 1 < g_imageSize; i++) {
        if (base[i] != (uint8_t)str[0] || (i && base[i - 1] != 0)) continue;
        if (memcmp(base + i, str, len + 1) == 0)
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

// Resolve the member offset a UI "selector-..." body attribute is bound to.
// The engine registers each selector attribute with a global descriptor:
//     LEA RDX,[attr-string]; LEA RCX,[DESCRIPTOR]; JMP registerFn      (thunk)
// and the owning control binds it to a member in its bind function:
//     LEA R8,[this+OFFSET]; LEA R9,[rip -> DESCRIPTOR]; CALL BindSelector
// Returns OFFSET, or 0 if any link is missing or the offset is ambiguous
// (multiple bind sites with different offsets).
// Step 2 of the selector chain, for ONE descriptor: its bind sites
//     LEA R8,[this+OFFSET]; LEA R9,[rip -> DESCRIPTOR]; CALL BindSelector
// Returns OFFSET when every bind site agrees on a single value, else 0.
static uint32_t BindOffsetForDescriptor(uintptr_t desc) {
    uint32_t offs[8]; int nOffs = 0;
    uint8_t* base = (uint8_t*)g_gameBase;
    for (DWORD i = 0x40; i + 7 < g_imageSize; i++) {   // 0x40: keep the back-walk inside the image
        uint8_t* p = base + i;
        if (p[0] != 0x4C || p[1] != 0x8D || p[2] != 0x0D) continue;
        int32_t disp = *(int32_t*)(p + 3);
        if ((uintptr_t)(p + 7) + disp != desc) continue;
        for (int b = 3; b <= 0x20; b++) {                     // walk back for LEA R8,[reg+disp]
            uint8_t* q = p - b;
            if ((q[0] != 0x4C && q[0] != 0x4D) || q[1] != 0x8D) continue;
            uint8_t modrm = q[2];
            if (((modrm >> 3) & 7) != 0) continue;            // reg field must be R8
            uint8_t mod = modrm & 0xC0, rm = modrm & 7;
            if (rm == 4) continue;                            // skip SIB ([rsp+...])
            uint32_t off;
            if (mod == 0x40) {                                // disp8 (signed — reject negative)
                if (q[3] >= 0x80) continue;
                off = q[3];
            }
            else if (mod == 0x80) off = *(uint32_t*)(q + 3);  // disp32
            else continue;
            if (off < 0x10 || off >= 0x2000) continue;
            bool dup = false;
            for (int k = 0; k < nOffs; k++) if (offs[k] == off) dup = true;
            if (!dup && nOffs < 8) offs[nOffs++] = off;
            break;
        }
    }
    return (nOffs == 1) ? offs[0] : 0;
}

static uint32_t ResolveSelectorMemberOffset(const char* attrName) {
    uintptr_t strVA = FindString(attrName);
    if (!strVA) return 0;
    // 1) registration thunks: LEA RDX,[rip->string]; MOV r8d,1; LEA RCX,[rip->descriptor];
    //    JMP registerFn. The descriptor LEA always FOLLOWS the string LEA inside
    //    the same thunk; never scan backwards (thunks are packed at a 0x20 stride).
    //    Since 2.01 the SAME attribute name is registered by more than one control
    //    class (one descriptor each) and only the class that really binds it has
    //    bind sites: "selector-title-subtext-stage" has descriptor A without any
    //    bind site and descriptor B bound at +0xF0. So walk every thunk instead of
    //    stopping at the first descriptor, and require the binding ones to agree.
    uint32_t result = 0;
    uintptr_t lea = 0;
    for (int guard = 0; guard < 8; guard++) {
        lea = FindLEA(strVA, lea ? lea + 1 : 0);
        if (!lea) break;
        uintptr_t desc = 0;
        for (int d = 1; d <= 0x20; d++) {
            uint8_t* p = (uint8_t*)(lea + d);
            if (p[0] == 0x48 && p[1] == 0x8D && p[2] == 0x0D) {   // LEA RCX,[rip+disp32]
                int32_t disp = *(int32_t*)(p + 3);
                uintptr_t t = (uintptr_t)(p + 7) + disp;
                if (t > g_gameBase && t < g_gameBase + g_imageSize) { desc = t; break; }
            }
        }
        if (!desc) continue;
        uint32_t off = BindOffsetForDescriptor(desc);
        if (!off) continue;
        if (result && result != off) return 0;   // two binding classes disagree
        result = off;
    }
    return result;
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
        // mov [rsp+disp8], rbx  (48 89 5C 24 XX) — any stack slot, common prolog
        if (p[0] == 0x48 && p[1] == 0x89 && p[2] == 0x5C && p[3] == 0x24)
            return (uintptr_t)p;
        // REX push rbp  (40 55)
        if (p[0] == 0x40 && p[1] == 0x55)
            return (uintptr_t)p;
        // REX push rsi  (40 56) — seen in small UI helpers like FUN_140b99b40
        if (p[0] == 0x40 && p[1] == 0x56)
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
        if (!g_hXInput) continue;

        // Prefer ordinal 100 = XInputGetStateEx (undocumented, returns Guide
        // button + reads from the *fresh* slot rather than the cached
        // legacy slot). xinput9_1_0.dll has no ordinal 100 — fall through.
        g_pXInputGetState = (PFN_XInputGetState)GetProcAddress(g_hXInput, (LPCSTR)100);
        if (!g_pXInputGetState) {
            g_pXInputGetState = (PFN_XInputGetState)GetProcAddress(g_hXInput, "XInputGetState");
        }
        if (g_pXInputGetState) return true;
        FreeLibrary(g_hXInput);
        g_hXInput = nullptr;
    }
    return false;
}

// ============================================================
//  XInput IAT hook on game module
//
//  The game polls XInput from its own thread independently of the
//  mod. While the warehouse is open, that polling makes the game
//  treat B as Dodge and react to LB+LeftStick / similar combos —
//  the controller user gets a dodge roll on close and the open is
//  fought by the game's own input handling. (DirectInput / Sony HID
//  doesn't have this problem because the game's UI-cancel path
//  consumes Circle on the WM_INPUT route.)
//
//  Fix: IAT-hook XInputGetState on CrimsonDesert.exe so the GAME's
//  XInput reads come through us. The mod's own poll uses the direct
//  DLL export (g_pXInputGetState) which is not affected by the IAT.
//
//  Filter rules:
//    - while warehouse is mod-owned: clear B (no dodge) — unless a dialog
//      is up, which the game must be able to cancel with B;
//      clear configured per-panel buttons + their modifiers when
//      both are held (so combos that are bound to mod-actions never
//      reach the game)
//    - while warehouse is closed: clear the configured per-panel
//      combo only when both modifier+button are held simultaneously.
//      This way LB or LeftStick alone still work for game functions.
// ============================================================
static volatile PVOID  g_xinputIATSlot = nullptr;
static PFN_XInputGetState g_origXInputGetState_IAT = nullptr;

extern "C" DWORD WINAPI XInputGetState_Filtered(DWORD slot, XINPUT_STATE_LOCAL* state) {
    PFN_XInputGetState orig = g_origXInputGetState_IAT;
    if (!orig) return 1;
    DWORD r = orig(slot, state);
    if (r != 0 || !state || slot != 0) return r;

    WORD btns = state->Gamepad.wButtons;
    WORD clear = 0;

    // Per-panel combo masking: when modifier+button are both held,
    // hide the combo from the game so it can't react to it.
    for (int i = 0; i < PANEL_COUNT; i++) {
        WORD btn = g_panels[i].controllerButton;
        if (!btn || !(btns & btn)) continue;
        WORD modBit = g_panels[i].controllerModifier;
        if (modBit && !(btns & modBit)) continue;
        clear |= btn;
        if (modBit) clear |= modBit;
    }

    // B masked while the warehouse is mod-owned (no dodge) — except while a
    // dialog is up, which the game has to be able to cancel with B.
    if (InterlockedCompareExchange(&g_warehouseActive, 0, 0) && !IsNewModalDialogVisible())
        clear |= 0x2000;

    state->Gamepad.wButtons = btns & ~clear;
    return r;
}

static bool InstallXInputIATHook(HMODULE gameModule) {
    if (!gameModule || g_xinputIATSlot) return false;
    auto* dos = (IMAGE_DOS_HEADER*)gameModule;
    if (dos->e_magic != IMAGE_DOS_SIGNATURE) return false;
    auto* nt = (IMAGE_NT_HEADERS*)((BYTE*)gameModule + dos->e_lfanew);
    if (nt->Signature != IMAGE_NT_SIGNATURE) return false;
    auto& dir = nt->OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_IMPORT];
    if (!dir.VirtualAddress) return false;

    auto* desc = (IMAGE_IMPORT_DESCRIPTOR*)((BYTE*)gameModule + dir.VirtualAddress);
    BYTE* base = (BYTE*)gameModule;
    for (; desc->Name; desc++) {
        const char* dllName = (const char*)(base + desc->Name);
        if (_strnicmp(dllName, "xinput", 6) != 0) continue;
        auto* origThunk = (IMAGE_THUNK_DATA*)(base + desc->OriginalFirstThunk);
        auto* iatThunk  = (IMAGE_THUNK_DATA*)(base + desc->FirstThunk);
        if (!origThunk->u1.AddressOfData) {
            // Bound import — OriginalFirstThunk may be 0; fall back to FirstThunk for names
            origThunk = iatThunk;
        }
        for (; origThunk->u1.AddressOfData; origThunk++, iatThunk++) {
            if (origThunk->u1.Ordinal & IMAGE_ORDINAL_FLAG64) continue;
            auto* byName = (IMAGE_IMPORT_BY_NAME*)(base + origThunk->u1.AddressOfData);
            if (strcmp((char*)byName->Name, "XInputGetState") != 0) continue;

            DWORD oldProt;
            if (!VirtualProtect(&iatThunk->u1.Function, sizeof(void*),
                                PAGE_READWRITE, &oldProt)) {
                return false;
            }
            g_origXInputGetState_IAT = (PFN_XInputGetState)(uintptr_t)iatThunk->u1.Function;
            iatThunk->u1.Function = (ULONGLONG)(uintptr_t)&XInputGetState_Filtered;
            VirtualProtect(&iatThunk->u1.Function, sizeof(void*), oldProt, &oldProt);
            g_xinputIATSlot = &iatThunk->u1.Function;
            return true;
        }
    }
    return false;
}

static void RemoveXInputIATHook() {
    if (!g_xinputIATSlot || !g_origXInputGetState_IAT) return;
    DWORD oldProt;
    if (VirtualProtect((LPVOID)g_xinputIATSlot, sizeof(void*),
                       PAGE_READWRITE, &oldProt)) {
        *(ULONGLONG*)g_xinputIATSlot = (ULONGLONG)(uintptr_t)g_origXInputGetState_IAT;
        VirtualProtect((LPVOID)g_xinputIATSlot, sizeof(void*), oldProt, &oldProt);
    }
    g_xinputIATSlot = nullptr;
}

// ============================================================
//  Game Hooks
// ============================================================
extern "C" void __fastcall CaptureOnHandler(void* thisPtr, void* rdx, void* r8, void* r9) {
    InterlockedIncrement(&g_handlerHitCount);
    if (g_handlerHitCount == 1 && !g_handlerThis) {
        InterlockedExchange64(&g_handlerThis, (LONG64)(uintptr_t)thisPtr);
        Log("CAPTURED warehouse controller via handler: 0x%llX",
            (unsigned long long)(uintptr_t)thisPtr);
        __try {
            // A vtable mismatch means HookedCanShow will never recognise this
            // object and the panel cannot render — worth one log line.
            uintptr_t capturedVt = *(uintptr_t*)thisPtr;
            Log("  Captured vtable: base+0x%llX — %s warehouse vtable base+0x%llX",
                capturedVt > g_gameBase ? (unsigned long long)(capturedVt - g_gameBase) : (unsigned long long)capturedVt,
                (capturedVt == g_warehouseVtableStart) ? "MATCHES" : "MISMATCH vs",
                g_warehouseVtableStart > g_gameBase ? (unsigned long long)(g_warehouseVtableStart - g_gameBase) : 0ULL);
        } __except(EXCEPTION_EXECUTE_HANDLER) {}

        // If a F-key trigger is currently waiting on init (warehouse object
        // was lazy-instantiated by the game after our F-press), run init
        // inline on the game thread NOW — mirrors HookedCanShow's first-open
        // fix. Without this, the deferred WM_INIT_WAREHOUSE poll in
        // InputThread may have already timed out by the time the game
        // instantiates the warehouse, leaving the user with no panel even
        // after Handler captured. Re-entrant Handler calls from inside
        // InitWarehousePanel are safe because g_handlerHitCount > 1 on the
        // re-entry path, so this capture block does NOT fire recursively.
        if (InterlockedCompareExchange(&g_initPending, 0, 0)) {
            InterlockedExchange(&g_initPending, 0);
            Log("  Handler-hook capture: running InitWarehousePanel inline (lazy-instantiation fix)");
            InitWarehousePanel((uintptr_t)thisPtr, GetInitStringForActive());
        }
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

// ============================================================
//  InventoryInfo manager, resolved through RTTI
// ============================================================
// The manager singleton lives in one global. No code anchor for it survives
// across updates (the singleton load moves between functions), but RTTI gives
// a path that depends on no register allocation and no struct offset at all:
//
//   ".?AVInventoryInfoManager@pa@@"  -> TypeDescriptor (name - 0x10)
//   -> CompleteObjectLocator (signature 1 at +0x00, TD rva at +0x0C)
//   -> the qword that points at the COL; the vtable starts 8 bytes after it
//   -> vtable[2] is  MOV [rip+disp32], RCX ; RET   (the instance setter)
//   -> vtable[3] is  MOV [rip+disp32], 0   ; RET   (the clearer)
//
// Both slots must decode to the SAME global — that is the cross-check, and it
// is what makes this safe to write through.
//
// Layout (Ghidra FUN_140432c20 = GetInventoryInfo, confirmed in the running
// game against gamedata/inventory.staticinfobody):
//     mgr+0x08  u32   record count (21)
//     mgr+0x28  ptr   index table, {u32 file id, u32 body offset} per record
//     mgr+0x58  ptr   array of InventoryInfo*, indexed by POSITION in that table
//     info+0x48 u16   base slot count (housing chests 10)
//     info+0x4A u16   maximum         (housing chests 1000)
// Records are created lazily; a NULL entry means "not loaded yet", so the walk
// must skip and retry rather than stop.
static uintptr_t g_invMgrGlobal = 0;
static uint32_t  g_invSlotFieldOff = 0x48;

static uintptr_t DecodeSetterGlobal(uintptr_t fn) {
    __try {
        const uint8_t* q = (const uint8_t*)fn;
        // 48 89 0D <disp32> C3   -> mov [rip+d], rcx ; ret
        if (q[0] == 0x48 && q[1] == 0x89 && q[2] == 0x0D && q[7] == 0xC3)
            return fn + 7 + *(int32_t*)(q + 3);
        // 48 C7 05 <disp32> 00000000 C3  -> mov qword [rip+d], 0 ; ret
        if (q[0] == 0x48 && q[1] == 0xC7 && q[2] == 0x05 && q[11] == 0xC3)
            return fn + 11 + *(int32_t*)(q + 3);
    } __except(EXCEPTION_EXECUTE_HANDLER) {}
    return 0;
}

static bool ResolveInventoryMgrViaRtti() {
    if (g_invMgrGlobal) return true;
    uintptr_t nameAddr = FindString(".?AVInventoryInfoManager@pa@@");
    if (!nameAddr) { Log("InvMgr: RTTI name not found"); return false; }
    uint32_t tdRva = (uint32_t)(nameAddr - 0x10 - g_gameBase);

    uint8_t* base = (uint8_t*)g_gameBase;
    uintptr_t col = 0;
    for (DWORD i = 0; (size_t)i + 0x18 < g_imageSize; i += 4) {
        if (*(uint32_t*)(base + i + 0x0C) != tdRva) continue;
        if (*(uint32_t*)(base + i) != 1) continue;          // COL signature
        col = g_gameBase + i;
        break;
    }
    if (!col) { Log("InvMgr: CompleteObjectLocator not found"); return false; }

    uintptr_t vtable = 0;
    for (DWORD i = 0; (size_t)i + 16 < g_imageSize; i += 8) {
        if (*(uintptr_t*)(base + i) == col) { vtable = g_gameBase + i + 8; break; }
    }
    if (!vtable) { Log("InvMgr: vtable for the COL not found"); return false; }

    uintptr_t gSet = 0, gClear = 0;
    __try {
        gSet   = DecodeSetterGlobal(*(uintptr_t*)(vtable + 2 * 8));
        gClear = DecodeSetterGlobal(*(uintptr_t*)(vtable + 3 * 8));
    } __except(EXCEPTION_EXECUTE_HANDLER) {}

    if (!gSet || gSet != gClear) {
        Log("InvMgr: setter/clearer disagree (set=0x%llX clear=0x%llX) — refusing",
            (unsigned long long)gSet, (unsigned long long)gClear);
        return false;
    }
    g_invMgrGlobal = gSet;
    Log("InvMgr: OK global=base+0x%llX (RTTI -> vtable base+0x%llX, slots 2 and 3 agree)",
        (unsigned long long)(gSet - g_gameBase),
        (unsigned long long)(vtable - g_gameBase));
    return true;
}

// The InventoryInfo manager indexes its record array by POSITION in the index
// table at mgr+0x28 (one {u32 id, u32 offset} entry per record, in file order),
// not by the id stored in the data file. The file ids start at 1, so
// Housing_Dresser (file id 0x0F) is arr[0x0E] at runtime. Earlier versions
// assumed index == id and therefore raised the five records AFTER the dresser
// (fridge, symbol, collecting, materials, BirdFeed) while the dresser kept its
// 10 — the F6 bug. Resolve every chest through the table instead.
static uint16_t RuntimeIndexForFileId(uint16_t fileId) {
    if (!g_invMgrGlobal) return 0xFFFF;
    __try {
        uintptr_t mgr = *(uintptr_t*)g_invMgrGlobal;
        if (mgr <= 0x10000) return 0xFFFF;
        uint32_t count = *(uint32_t*)(mgr + 0x08);
        uintptr_t tbl = *(uintptr_t*)(mgr + 0x28);
        if (tbl <= 0x10000 || count == 0 || count > 4096) return 0xFFFF;
        for (uint32_t i = 0; i < count; i++)
            if (*(uint16_t*)(tbl + (uintptr_t)i * 8) == fileId) return (uint16_t)i;
    } __except(EXCEPTION_EXECUTE_HANDLER) {}
    return 0xFFFF;
}

static uint16_t FileIdForRuntimeIndex(uint16_t idx) {
    if (!g_invMgrGlobal) return 0xFFFF;
    __try {
        uintptr_t mgr = *(uintptr_t*)g_invMgrGlobal;
        if (mgr <= 0x10000) return 0xFFFF;
        uint32_t count = *(uint32_t*)(mgr + 0x08);
        uintptr_t tbl = *(uintptr_t*)(mgr + 0x28);
        if (tbl <= 0x10000 || idx >= count) return 0xFFFF;
        return *(uint16_t*)(tbl + (uintptr_t)idx * 8);
    } __except(EXCEPTION_EXECUTE_HANDLER) {}
    return 0xFFFF;
}

// Record names by FILE id (gamedata/inventory.staticinfoheader + body, 2.01.00).
// Only used for logging; nothing is resolved through this table.
static const char* InvNameForFileId(uint16_t fileId) {
    static const char* const kNames[] = {
        "?", "Money", "Character", "PearlUser", "PearlCharacter", "Quest",
        "Wagon", "PetAndVehicle", "CampWareHouse", "WareHouse", "Bank",
        "CampStraw", "Recovery", "Kuku", "InvisibleInventory", "Housing_Dresser",
        "Housing_Refrigerator", "Housing_Symbol", "Housing_Collecting",
        "Housing_GatheredMaterials", "BirdFeed", "Ship",
    };
    return (fileId < sizeof(kNames) / sizeof(kNames[0])) ? kNames[fileId] : "?";
}

// Confirm the field offset by content before writing anything: two housing
// chests (Dresser, Refrigerator) must read 10/1000 at the same offset.
static bool ValidateSlotField(uintptr_t arr, uint32_t count, uint32_t off) {
    __try {
        if (0x13 >= count) return false;
        uint16_t iD = RuntimeIndexForFileId(0x0F), iF = RuntimeIndexForFileId(0x10);
        if (iD == 0xFFFF || iF == 0xFFFF || iD >= count || iF >= count) return false;
        uintptr_t dres = *(uintptr_t*)(arr + (uintptr_t)iD * 8);
        uintptr_t frig = *(uintptr_t*)(arr + (uintptr_t)iF * 8);
        if (!dres || !frig) return false;
        // Two housing chests reading 10 / 1000 at the SAME offset pins both the
        // field position and its meaning. Two independent records agreeing is
        // specific enough; a third condition is not worth its risk.
        //
        // Deliberately NOT checked: the camp warehouse. Its capacity depends on
        // the camp upgrade level, so it differs per save and changes over time.
        if (*(uint16_t*)(dres + off) != 10 || *(uint16_t*)(dres + off + 2) != 1000) return false;
        if (*(uint16_t*)(frig + off) != 10 || *(uint16_t*)(frig + off + 2) != 1000) return false;
        return true;
    } __except(EXCEPTION_EXECUTE_HANDLER) {}
    return false;
}

// Read one record's base slot count (info+0x48) by runtime index; for the open log.
static int ReadChestSlots(uint16_t id) {
    if (!g_invMgrGlobal) return -1;
    __try {
        uintptr_t mgr = *(uintptr_t*)g_invMgrGlobal;
        if (mgr <= 0x10000) return -1;
        uint32_t count = *(uint32_t*)(mgr + 0x08);
        uintptr_t arr = *(uintptr_t*)(mgr + 0x58);
        if (!arr || id >= count) return -1;
        uintptr_t info = *(uintptr_t*)(arr + (uintptr_t)id * 8);
        if (!info) return -2;
        return (int)*(uint16_t*)(info + g_invSlotFieldOff);
    } __except(EXCEPTION_EXECUTE_HANDLER) {}
    return -1;
}


// ---------------------------------------------------------------------------
// Live inventory groups (2.01.00, from Ghidra):
//   FUN_142073710  container = *(*(actor + 0x68) + 0xB8); container+0x08 points
//                  back to the actor, +0x18 = array of group pointers, +0x20 = count.
//   FUN_14234e0c0  furniture bonus: +0x14 = min(+0x16 + info->0x48 + delta, info->0x4A);
//                  +0x16 += delta; +0x18 += growth. Nothing else is written.
//   FUN_14207ed50  housing re-seed: +0x16 = bonus; +0x14 = bonus + info->0x48.
//   FUN_14234e1f0  group: +0x00 entries (0xC8 each: +8 item key, +0x10 count),
//                  +0x08 / +0x0C entry counts, +0x10 u16 type id, +0x12 used.
// The record (info+0x48) only seeds the group; what the panel shows is the
// group's +0x14. With the record patched before the save loads, the game seeds
// every housing group at the maximum itself; PatchGroupCapacities() is the
// safety net for a save that was already loaded when the patch ran.
// Validate one actor candidate: container = *(*(actor+0x68)+0xB8) has to point
// back to the actor at +0x08 and hold a sane group array (distinct type ids).
static uintptr_t ContainerOfActor(uintptr_t actor) {
    if (actor <= 0x10000 || actor >= 0x7FFFFFFFFFFFULL) return 0;
    __try {
        uintptr_t owner = *(uintptr_t*)(actor + 0x68);
        if (owner <= 0x10000 || owner >= 0x7FFFFFFFFFFFULL) return 0;
        uintptr_t cont = *(uintptr_t*)(owner + 0xB8);
        if (cont <= 0x10000 || cont >= 0x7FFFFFFFFFFFULL) return 0;
        if (*(uintptr_t*)(cont + 0x08) != actor) return 0;
        uint32_t n = *(uint32_t*)(cont + 0x20);
        uintptr_t arr = *(uintptr_t*)(cont + 0x18);
        if (n == 0 || n > 64 || arr <= 0x10000 || arr >= 0x7FFFFFFFFFFFULL) return 0;
        uint32_t seen = 0;
        for (uint32_t i = 0; i < n; i++) {
            uintptr_t g = *(uintptr_t*)(arr + (uintptr_t)i * 8);
            if (g <= 0x10000 || g >= 0x7FFFFFFFFFFFULL) return 0;
            uint16_t key = *(uint16_t*)(g + 0x10);
            if (key >= 32 || (seen & (1u << key))) return 0;
            seen |= 1u << key;
        }
        return cont;
    } __except(EXCEPTION_EXECUTE_HANDLER) {}
    return 0;
}

// The player actor the game's own inventory code starts from
// (FUN_1405dd4a0 -> FUN_14083d050):  actor = *(*(G + 0x30) + 0x50), where G is
// the session global (2.01.00: DAT_146c29760, resolved into g_sessionGlobal).
static uintptr_t ActorViaSessionGlobal(uintptr_t G) {
    __try {
        uintptr_t sess = *(uintptr_t*)G;
        if (sess <= 0x10000 || sess >= 0x7FFFFFFFFFFFULL) return 0;
        uintptr_t pl = *(uintptr_t*)(sess + 0x30);
        if (pl <= 0x10000 || pl >= 0x7FFFFFFFFFFFULL) return 0;
        return *(uintptr_t*)(pl + 0x50);
    } __except(EXCEPTION_EXECUTE_HANDLER) {}
    return 0;
}

static uintptr_t g_sessionGlobal = 0;   // resolved in ResolveAddresses (dominant "+0x30" global)
static uintptr_t g_invContainer = 0, g_invActor = 0;

// Every candidate goes through ContainerOfActor(): the container must point
// back at the actor and hold a group array with distinct small type ids. That
// check is what makes a wrong global harmless — it simply fails to validate.
static uintptr_t ResolveInvContainer() {
    if (g_invContainer && ContainerOfActor(g_invActor) == g_invContainer) return g_invContainer;
    g_invContainer = 0;
    uintptr_t actor = 0, cont = 0, viaG = 0;
    const char* how = "";
    // 1) the session global the game's own inventory code uses
    if (g_sessionGlobal) {
        viaG  = g_sessionGlobal;
        actor = ActorViaSessionGlobal(viaG);
        cont  = ContainerOfActor(actor);
        if (cont) how = "session global";
    }
    // 2) any global in the singleton cluster around the game manager with the
    //    same shape (the session global sits 0x510 below it on 2.01.00)
    if (!cont && g_mainCharGlobalPtr) {
        uintptr_t lo = g_mainCharGlobalPtr - 0x2000, hi = g_mainCharGlobalPtr + 0x2000;
        if (lo < g_gameBase) lo = g_gameBase;
        if (hi > g_gameBase + g_imageSize - 8) hi = g_gameBase + g_imageSize - 8;
        for (uintptr_t G = lo; G < hi && !cont; G += 8) {
            actor = ActorViaSessionGlobal(G);
            cont  = ContainerOfActor(actor);
            if (cont) { viaG = G; how = "cluster scan"; }
        }
    }
    static bool logged = false, loggedFail = false;
    if (cont) {
        g_invContainer = cont; g_invActor = actor;
        if (!logged) { logged = true;
            Log("InvGroups: container=0x%llX actor=0x%llX groups=%u via %s (base+0x%llX)",
                (unsigned long long)cont, (unsigned long long)actor, *(uint32_t*)(cont + 0x20),
                how, (unsigned long long)(viaG - g_gameBase)); }
    } else if (!loggedFail) {
        loggedFail = true;
        Log("InvGroups: no actor/container yet (session global base+0x%llX -> actor 0x%llX)",
            g_sessionGlobal ? (unsigned long long)(g_sessionGlobal - g_gameBase) : 0ULL,
            (unsigned long long)(g_sessionGlobal ? ActorViaSessionGlobal(g_sessionGlobal) : 0));
    }
    return cont;
}

static uintptr_t FindInvGroup(uintptr_t cont, uint16_t id) {
    __try {
        uint32_t n = *(uint32_t*)(cont + 0x20);
        uintptr_t arr = *(uintptr_t*)(cont + 0x18);
        for (uint32_t i = 0; i < n; i++) {
            uintptr_t g = *(uintptr_t*)(arr + (uintptr_t)i * 8);
            if (g > 0x10000 && *(uint16_t*)(g + 0x10) == id) return g;
        }
    } __except(EXCEPTION_EXECUTE_HANDLER) {}
    return 0;
}

static void LogInvGroup(const char* tag, uintptr_t g) {
    __try {
        Log("  %s group 0x%llX: id=0x%02X entries=0x%llX size=%d cap=%d used=%d "
            "slots=%u bonus=%u f18=%u last=%u",
            tag, (unsigned long long)g, *(uint16_t*)(g + 0x10),
            (unsigned long long)*(uintptr_t*)g,
            (int)*(int16_t*)(g + 0x08), (int)*(int16_t*)(g + 0x0C), (int)*(int16_t*)(g + 0x12),
            *(uint16_t*)(g + 0x14), *(uint16_t*)(g + 0x16),
            *(uint16_t*)(g + 0x18), *(uint16_t*)(g + 0x1A));
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        Log("  %s group 0x%llX: unreadable", tag, (unsigned long long)g);
    }
}

static void DumpInvGroups() {
    uintptr_t cont = ResolveInvContainer();
    if (!cont) {
        Log("InvGroups: container not resolved");
        return;
    }
    __try {
        uint32_t n = *(uint32_t*)(cont + 0x20);
        uintptr_t arr = *(uintptr_t*)(cont + 0x18);
        Log("InvGroups: container=0x%llX groups=%u", (unsigned long long)cont, n);
        for (uint32_t i = 0; i < n; i++) {
            uintptr_t g = *(uintptr_t*)(arr + (uintptr_t)i * 8);
            if (g > 0x10000) {
                uint16_t rt = *(uint16_t*)(g + 0x10);
                uint16_t fileId = FileIdForRuntimeIndex(rt);
                char tag[80];
                snprintf(tag, sizeof(tag), "[file 0x%02X %s]", fileId, InvNameForFileId(fileId));
                LogInvGroup(tag, g);
            }
            else Log("  group[%u] = 0x%llX", i, (unsigned long long)g);
        }
    } __except(EXCEPTION_EXECUTE_HANDLER) { Log("InvGroups: EXCEPTION"); }
}

// Raise the live capacity of the five housing chests to the record maximum
// (info+0x4A) the way the game's own bonus path does: growth = max - slots;
// slots = max; bonus += growth; +0x18 += growth. CampWareHouse (0x08) is left
// alone. openingId selects which group gets a before/after line. Only called
// from InitWarehousePanel (on open).
static int PatchGroupCapacities(uint16_t openingId) {
    uintptr_t cont = ResolveInvContainer();
    if (!cont || !g_invMgrGlobal) return 0;
    static const uint16_t kIds[] = { 0x0F, 0x10, 0x11, 0x12, 0x13 };   // FILE ids
    int raised = 0;
    __try {
        uintptr_t mgr = *(uintptr_t*)g_invMgrGlobal;
        if (mgr <= 0x10000) return 0;
        uint32_t count = *(uint32_t*)(mgr + 0x08);
        uintptr_t infoArr = *(uintptr_t*)(mgr + 0x58);
        for (int k = 0; k < 5; k++) {
            uint16_t id = RuntimeIndexForFileId(kIds[k]);   // file id -> runtime index
            if (id == 0xFFFF) continue;
            if (id >= count) continue;
            uintptr_t info = *(uintptr_t*)(infoArr + (uintptr_t)id * 8);
            uintptr_t g = FindInvGroup(cont, id);
            if (!info || !g) {
                if (id == openingId)
                    Log("  InvGroups: id 0x%02X info=0x%llX group=0x%llX — not raised",
                        id, (unsigned long long)info, (unsigned long long)g);
                continue;
            }
            uint16_t max = *(uint16_t*)(info + 0x4A);
            uint16_t cur = *(uint16_t*)(g + 0x14);
            if (id == openingId) LogInvGroup("before", g);
            if (max == 0 || max > 5000 || cur >= max) continue;
            uint16_t growth = (uint16_t)(max - cur);
            *(uint16_t*)(g + 0x14) = max;
            *(uint16_t*)(g + 0x16) = (uint16_t)(*(uint16_t*)(g + 0x16) + growth);
            *(uint16_t*)(g + 0x18) = (uint16_t)(*(uint16_t*)(g + 0x18) + growth);
            raised++;
            Log("  InvGroups: id 0x%02X live slots %u -> %u", id, cur, max);
            if (id == openingId) LogInvGroup("after ", g);
        }
    } __except(EXCEPTION_EXECUTE_HANDLER) { Log("InvGroups: EXCEPTION while patching"); }
    return raised;
}

// Raise the five housing records (info+0x48) to their own maximum (info+0x4A).
// Returns the number of chests handled (patched or already at max) once every
// record is loaded, else 0 so the caller keeps polling. CampWareHouse and
// InvisibleInventory are never in the list.
static int PatchSlotsViaManager() {
    if (!g_invMgrGlobal) return 0;
    static const struct { uint16_t id; const char* name; } kChests[] = {
        { 0x0F, "Housing_Dresser" }, { 0x10, "Housing_Refrigerator" },
        { 0x11, "Housing_Symbol" },  { 0x12, "Housing_Collecting" },
        { 0x13, "Housing_GatheredMaterials" },
        // CampWareHouse (id 0x08) is deliberately left at its 240.
    };
    int patched = 0;
    int done = 0;
    bool allDone = true;
    __try {
        uintptr_t mgr = *(uintptr_t*)g_invMgrGlobal;
        static int reportCount = 0;
        if (mgr <= 0x10000) {
            if (reportCount < 3) { reportCount++; Log("InvMgr: instance not created yet (global holds 0x%llX)", (unsigned long long)mgr); }
            return 0;
        }
        uint32_t count = *(uint32_t*)(mgr + 0x08);
        uintptr_t arr  = *(uintptr_t*)(mgr + 0x58);
        static bool mgrLogged = false;
        if (!mgrLogged) {
            mgrLogged = true;
            Log("InvMgr: instance=0x%llX  count(+0x08)=%u  array(+0x58)=0x%llX",
                (unsigned long long)mgr, count, (unsigned long long)arr);
        }
        if (!arr || count == 0 || count > 4096) return 0;

        static bool fieldOk = false;
        if (!fieldOk) {
            if (ValidateSlotField(arr, count, 0x48)) {
                g_invSlotFieldOff = 0x48;
                fieldOk = true;
            } else {
                // The struct may shift again; find the offset that satisfies the
                // same content test rather than trusting 0x48.
                for (uint32_t o = 0; o <= 0x200 && !fieldOk; o += 2)
                    if (ValidateSlotField(arr, count, o)) {
                        g_invSlotFieldOff = o;
                        fieldOk = true;
                    }
            }
            if (!fieldOk) return 0;                          // stay silent, retry later
            Log("InvMgr: table OK — count=%u array=0x%llX slot field at info+0x%X "
                "(validated: Dresser and Refrigerator read 10/1000)",
                count, (unsigned long long)arr, g_invSlotFieldOff);
        }

        static bool tableLogged = false;
        if (!tableLogged) {
            tableLogged = true;
            for (int c = 0; c < 5; c++) {
                uint16_t rt = RuntimeIndexForFileId(kChests[c].id);
                uintptr_t info = (rt != 0xFFFF && rt < count) ? *(uintptr_t*)(arr + (uintptr_t)rt * 8) : 0;
                Log("  index: %s file id 0x%02X -> runtime 0x%02X (record 0x%llX)",
                    kChests[c].name, kChests[c].id, rt, (unsigned long long)info);
            }
        }
        for (int c = 0; c < 5; c++) {
            uint16_t rt = RuntimeIndexForFileId(kChests[c].id);
            if (rt == 0xFFFF || rt >= count) { allDone = false; continue; }
            uintptr_t info = *(uintptr_t*)(arr + (uintptr_t)rt * 8);
            if (!info) {
                // Entries are materialised lazily; some sit far from the others in
                // the table and appear only later. Report it once per chest so a
                // permanently missing entry is visible instead of silently costing
                // that chest its capacity, and let the worker retry.
                static bool nullLogged[5] = {};
                if (!nullLogged[c]) { nullLogged[c] = true;
                    Log("  slots: %s not loaded yet — will retry", kChests[c].name); }
                allDone = false;
                continue;
            }
            uint16_t* pSlots = (uint16_t*)(info + g_invSlotFieldOff);
            uint16_t maxSlots = *(uint16_t*)(info + g_invSlotFieldOff + 2);
            if (*pSlots == maxSlots) { done++; continue; }   // already at its maximum
            // Every housing record ships as 10/1000. Anything else means the data
            // changed; leave it alone and say so once.
            if (maxSlots != 1000 || *pSlots == 0 || *pSlots > maxSlots) {
                static bool oddLogged[5] = {};
                if (!oddLogged[c]) { oddLogged[c] = true;
                    Log("  slots: %s has %u/%u — unexpected, left alone",
                        kChests[c].name, (unsigned)*pSlots, (unsigned)maxSlots); }
                continue;
            }
            uint16_t before = *pSlots;
            DWORD oldProt = 0;
            bool unlocked = VirtualProtect(pSlots, 2, PAGE_READWRITE, &oldProt) != 0;
            *pSlots = maxSlots;
            if (unlocked) VirtualProtect(pSlots, 2, oldProt, &oldProt);
            patched++;
            Log("  slots: %s  %u -> %u", kChests[c].name, (unsigned)before, maxSlots);
        }
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        Log("InvMgr: EXCEPTION while patching");
        return 0;
    }
    if (patched) Log("Slot capacity: %d chest(s) raised%s", patched,
                     allDone ? "" : " (some entries still pending)");
    // Keep returning 0 while records are outstanding so the worker keeps
    // polling; chests already at their maximum count as handled.
    return allDone ? (patched > 0 ? patched : done) : 0;
}

// Fires whenever the game opens an ItemDetailModal ("View Details" popup);
// the hook sits on the "ItemDetailModalMessage" processor. The flag is
// cleared when ESC/B/Circle dismisses the popup or the warehouse closes.
extern "C" void __fastcall CaptureOnItemDetailCtor(void* /*param_1*/, void* /*param_2*/) {
    InterlockedExchange(&g_itemDetailActiveCount, 1);
    InterlockedExchange(&g_modalDismissed, 0);      // a new dialog is up again
    Log("ItemDetailModal opened");
}

// Fires when the game opens a quantity ("counting") dialog.
extern "C" void __fastcall CaptureOnCountingModal(void* /*param_1*/, void* /*param_2*/) {
    InterlockedExchange(&g_modalDismissed, 0);
    Log("CountingModal opened");
}

// Resolve mainChar from the game manager singleton: *(*(globalPtr) + 0x48)
static uintptr_t ResolveMainChar() {
    if (!g_mainCharGlobalPtr) return 0;
    __try {
        uintptr_t mgr = *(uintptr_t*)g_mainCharGlobalPtr;
        if (mgr) return *(uintptr_t*)(mgr + 0x48);
    } __except(EXCEPTION_EXECUTE_HANDLER) {}
    return 0;
}

// ============================================================
//  CanShow Hook
// ============================================================
typedef char (__fastcall *PFN_CanShow)(void*);
static PFN_CanShow g_origCanShow = nullptr;

extern "C" char __fastcall HookedCanShow(void* thisPtr) {
    uintptr_t handler = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);

    // Auto-capture the warehouse controller by exact vtable match. All six
    // storages share this controller — the per-panel inventory binding happens
    // via SetInventory in InitWarehousePanel.
    if (g_warehouseVtableStart && (uintptr_t)thisPtr != handler) {
        __try {
            if (*(uintptr_t*)thisPtr == g_warehouseVtableStart) {
                InterlockedExchange64(&g_handlerThis, (LONG64)(uintptr_t)thisPtr);
                handler = (uintptr_t)thisPtr;
                Log("AUTO-CAPTURED warehouse controller: 0x%llX", (unsigned long long)thisPtr);
                // First-open fix: when a hotkey press is waiting on this capture,
                // initialise the panel right now, on the game thread that is about
                // to render it. The WM_INIT_WAREHOUSE posted by InputThread later
                // becomes a no-op because g_initPending is cleared here.
                if (InterlockedCompareExchange(&g_initPending, 0, 0)) {
                    InterlockedExchange(&g_initPending, 0);
                    Log("  CanShow: running InitWarehousePanel inline (first-open fix)");
                    InitWarehousePanel(handler, GetInitStringForActive());
                }
            }
        } __except(EXCEPTION_EXECUTE_HANDLER) {}
    }

    if (InterlockedCompareExchange(&g_warehouseActive, 0, 0)) {
        // Handler not captured yet: we cannot tell the warehouse from other
        // panels, so let the game decide.
        if (handler == 0) return g_origCanShow(thisPtr);
        // The warehouse is force-shown for as long as the mod owns the session;
        // the only close paths are TriggerWarehouse (hotkey / ESC / controller).
        if ((uintptr_t)thisPtr == handler) return 1;
        // Suppress every other panel while the warehouse is open. Do NOT
        // delegate to the original here — its side effects make the warehouse
        // reappear during later NPC interactions.
        return 0;
    }
    return g_origCanShow(thisPtr);
}

// ============================================================
//  Hook Installation
// ============================================================

// Check if first N bytes contain RIP-relative instructions (ModRM.mod=00, R/M=101)
// that would break when relocated to a trampoline at a different address.
// NOTE: FF 25 (JMP [rip+disp32]) thunks are excluded — they work correctly in
// trampolines because the inline 8-byte target address is copied alongside.
// Opcodes (after optional REX) that take a single ModRM operand. RIP-
// relative addressing is signaled by ModRM (mod=00, r/m=101); a relocation
// would break the trampoline copy.
static bool IsModrmOpcode(uint8_t op) {
    // ALU r/m,r and r,r/m (8 op-pairs, 01..3B step 8 with +0/+2 variants)
    if (op == 0x01 || op == 0x03 || op == 0x09 || op == 0x0B ||
        op == 0x11 || op == 0x13 || op == 0x19 || op == 0x1B ||
        op == 0x21 || op == 0x23 || op == 0x29 || op == 0x2B ||
        op == 0x31 || op == 0x33 || op == 0x39 || op == 0x3B) return true;
    // 0x63 = MOVSXD, 0x85 = TEST, 0x87 = XCHG, 0x89/0x8B = MOV, 0x8D = LEA
    if (op == 0x63 || op == 0x85 || op == 0x87 ||
        op == 0x89 || op == 0x8B || op == 0x8D) return true;
    // 0x83 = ALU r/m, imm8 ; 0x81 = ALU r/m, imm32 ; 0xC6/C7 = MOV r/m, imm
    if (op == 0x83 || op == 0x81 || op == 0xC6 || op == 0xC7) return true;
    return false;
}

static bool ContainsRipRelative(uint8_t* code, int len) {
    for (int i = 0; i < len - 2; i++) {
        uint8_t b = code[i];
        // Non-REX: CALL [rip+disp32] = FF 15 xx xx xx xx (ModRM 0x15: mod=00, r/m=101)
        // (FF 25 is JMP thunk — safe to relocate because inline data follows, so skip it)
        if (b == 0xFF && i + 5 < len && code[i + 1] == 0x15) return true;
        // Non-REX MOV/LEA/ALU etc. with RIP-relative: opcode + ModRM(mod=00, r/m=101)
        if (IsModrmOpcode(b) && i + 5 < len && (code[i + 1] & 0xC7) == 0x05) return true;
        // REX-prefixed (0x40-0x4F): same checks on the byte after REX
        if (b >= 0x40 && b <= 0x4F && i + 2 < len) {
            uint8_t op = code[i + 1];
            if ((IsModrmOpcode(op) || op == 0x0F) && (code[i + 2] & 0xC7) == 0x05)
                return true;
            // REX + FF 15 (CALL [rip+disp32])
            if (op == 0xFF && i + 6 < len && code[i + 2] == 0x15) return true;
        }
    }
    return false;
}

// Decode a ModRM operand block length (not counting the opcode itself).
// Returns the number of bytes used by ModRM + optional SIB + optional disp.
// On x64, mod=00 / rm=101 is RIP-relative with a 4-byte displacement (NOT
// supported here as a hookable prolog instruction — caller should rely on
// ContainsRipRelative to abort, but the length calc is still correct).
static int ModRMLen(uint8_t modrm) {
    uint8_t mod = modrm >> 6;
    uint8_t rm  = modrm & 0x07;
    int sib  = (mod != 3 && rm == 4) ? 1 : 0;
    int disp = (mod == 0) ? (rm == 5 ? 4 : 0)  // RIP-relative at mod=0/rm=5
             : (mod == 1) ? 1
             : (mod == 2) ? 4
             :              0;                  // mod=3 → reg-reg, no disp
    return 1 + sib + disp;
}

// Find the smallest instruction boundary >= minBytes in a typical MSVC x86-64 prologue.
// Handles common prologue patterns: MOV [RSP+N], REG; PUSH; SUB RSP; LEA RBP; MOV RBP,RSP;
// CMP/TEST/XOR/SUB/ADD/AND/OR (ALU r/m,r and r,r/m); MOV r/m,imm32.
static int FindPrologBoundary(uint8_t* code, int minBytes) {
    int pos = 0;
    while (pos < minBytes && pos < 30) {
        uint8_t b = code[pos];
        // Single-byte PUSH: 50-57 (PUSH RAX..RDI)
        if (b >= 0x50 && b <= 0x57) { pos += 1; continue; }
        // REX.B + PUSH: 41 50-57 (PUSH R8..R15)
        if (b == 0x41 && code[pos+1] >= 0x50 && code[pos+1] <= 0x57) { pos += 2; continue; }
        // REX (empty) + PUSH: 40 50-57 (PUSH RAX..RDI with REX — MSVC emits this for RBP/RSI/RDI)
        if (b == 0x40 && code[pos+1] >= 0x50 && code[pos+1] <= 0x57) { pos += 2; continue; }
        // REX.W prefix (48..4F): all variants set REX.W=1 and differ only in
        // which register-extension bits (R/X/B) are set. Instruction-length
        // decoding is identical — only the register selection changes.
        if (b >= 0x48 && b <= 0x4F) {
            uint8_t op = code[pos+1];
            // ModRM-only ALU/MOV/TEST/XCHG/LEA ops (no immediate):
            //   01/03/09/0B/11/13/19/1B/21/23/29/2B/31/33/39/3B — ALU r/m,r and r,r/m
            //   85 (TEST), 87 (XCHG), 89 (MOV r/m,r), 8B (MOV r,r/m), 8D (LEA)
            bool modrmOnly =
                (op == 0x01) || (op == 0x03) || (op == 0x09) || (op == 0x0B) ||
                (op == 0x11) || (op == 0x13) || (op == 0x19) || (op == 0x1B) ||
                (op == 0x21) || (op == 0x23) || (op == 0x29) || (op == 0x2B) ||
                (op == 0x31) || (op == 0x33) || (op == 0x39) || (op == 0x3B) ||
                (op == 0x85) || (op == 0x87) || (op == 0x89) || (op == 0x8B) ||
                (op == 0x8D);
            // ALU r/m, imm8  (op group 1 with sign-extended byte)
            bool imm8  = (op == 0x83) || (op == 0xC6);
            // ALU r/m, imm32 (op group 1 with full dword)
            bool imm32 = (op == 0x81) || (op == 0xC7);
            // FF group (INC/DEC/CALL/JMP/PUSH r/m) — ModRM-only, sub-op in reg field
            bool ffGroup = (op == 0xFF);
            if (modrmOnly || imm8 || imm32 || ffGroup) {
                int operand = ModRMLen(code[pos+2]);
                int immLen  = imm8 ? 1 : imm32 ? 4 : 0;
                pos += 2 + operand + immLen;
                continue;
            }
        }
        // JMP [RIP+disp32] thunk: FF 25 xx xx xx xx + 8-byte inline address = 14 bytes
        if (b == 0xFF && code[pos+1] == 0x25) { pos += 14; continue; }
        // 66 89 modrm [sib] [disp] — operand-size override + MOV r/m16, r16
        // (e.g. `66 89 54 24 10` = MOV word ptr [RSP+0x10], DX before a PUSH chain).
        if (b == 0x66 && code[pos+1] == 0x89) {
            uint8_t modrm = code[pos+2];
            uint8_t mod = modrm >> 6, rm = modrm & 0x07;
            if (mod == 0x00) {
                if (rm == 0x05) { pos += 7; continue; }            // [rip+disp32]
                if (rm == 0x04) { pos += 4; continue; }            // [SIB]
                pos += 3; continue;                                // [reg]
            }
            if (mod == 0x01) { pos += 4 + (rm == 0x04 ? 1 : 0); continue; }  // [reg+disp8] (+SIB)
            if (mod == 0x02) { pos += 7 + (rm == 0x04 ? 1 : 0); continue; }  // [reg+disp32] (+SIB)
            if (mod == 0x03) { pos += 3; continue; }                          // reg,reg
        }
        // Unknown — bail out to avoid infinite loop
        Log("  FindPrologBoundary: unknown opcode 0x%02X at pos %d", b, pos);
        return 0;
    }
    return pos;
}

static bool InstallHook(uintptr_t func, uintptr_t capture, const char* name, int hookSize = 0) {
    // Auto-compute hook size if not provided: find instruction boundary >= 14 bytes
    if (hookSize <= 0) {
        hookSize = FindPrologBoundary((uint8_t*)func, 14);
        if (hookSize < 14 || hookSize > 28) {
            Log("HOOK %s: ABORT — cannot find clean instruction boundary (got %d) at base+0x%llX",
                name, hookSize, (unsigned long long)(func - g_gameBase));
            return false;
        }
    }
    // ALL size + capacity validation runs BEFORE the stack buffer copy: an
    // explicit hookSize > sizeof(orig) from a caller would overrun the local
    // buffer otherwise. (sizeof orig used here matches the actual buffer.)
    uint8_t orig[32];
    if (hookSize < 14 || hookSize > (int)sizeof(orig) ||
        hookSize > (int)sizeof(g_hookTable[0].orig) ||
        g_hookCount >= (int)(sizeof(g_hookTable)/sizeof(g_hookTable[0]))) {
        Log("HOOK %s: ABORT — invalid hookSize %d or hook-table full", name, hookSize);
        return false;
    }
    memcpy(orig, (void*)func, hookSize);
    if (ContainsRipRelative(orig, hookSize)) {
        Log("HOOK %s: ABORT — RIP-relative instruction in first %d bytes (base+0x%llX)",
            name, hookSize, (unsigned long long)(func - g_gameBase));
        return false;
    }
    void* thunk = VirtualAlloc(nullptr,256,MEM_COMMIT|MEM_RESERVE,PAGE_EXECUTE_READWRITE);
    if (!thunk) return false;
    uint8_t* t = (uint8_t*)thunk;
    uintptr_t ret = func + hookSize;
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
    memcpy(t,orig,hookSize); t+=hookSize;
    *t++=0xFF;*t++=0x25; *(uint32_t*)t=0; t+=4; *(uintptr_t*)t=ret; t+=8;
    DWORD op;
    VirtualProtect((void*)func,hookSize,PAGE_EXECUTE_READWRITE,&op);
    uint8_t* p=(uint8_t*)func;
    p[0]=0xFF;p[1]=0x25; *(uint32_t*)(p+2)=0; *(uintptr_t*)(p+6)=(uintptr_t)thunk;
    for (int i = 14; i < hookSize; i++) p[i] = 0x90; // NOP padding
    VirtualProtect((void*)func,hookSize,op,&op);
    FlushInstructionCache(GetCurrentProcess(),(void*)func,hookSize);
    g_hookTable[g_hookCount].addr = func;
    g_hookTable[g_hookCount].size = hookSize;
    memcpy(g_hookTable[g_hookCount].orig, orig, hookSize);
    g_hookCount++;
    Log("HOOK %s: OK base+0x%llX (size=%d)",name,(unsigned long long)(func-g_gameBase),hookSize);
    return true;
}

static bool InstallCanShowHook(uintptr_t func) {
    // Find a clean prolog boundary >= 14 bytes so the trampoline tail does not
    // sit mid-instruction; if the decoder meets an opcode it does not know,
    // fall back to a fixed 14-byte cut + NOP padding.
    int hookSize = FindPrologBoundary((uint8_t*)func, 14);
    if (hookSize < 14 || hookSize > 20) {
        Log("HOOK CanShow: prolog boundary not detected (got %d), falling back to fixed 14 bytes", hookSize);
        hookSize = 14;
    }
    // Reserve the table slot BEFORE patching so an overflow can't leave a
    // live patch that DLL_PROCESS_DETACH can never restore. Mirrors
    // InstallHook's contract.
    if (hookSize > (int)sizeof(g_hookTable[0].orig) ||
        g_hookCount >= (int)(sizeof(g_hookTable)/sizeof(g_hookTable[0]))) {
        Log("HOOK CanShow: ABORT — hook-table full or hookSize %d exceeds slot capacity", hookSize);
        return false;
    }
    uint8_t orig[20]; memcpy(orig, (void*)func, hookSize);
    if (ContainsRipRelative(orig, hookSize)) {
        Log("HOOK CanShow: ABORT — RIP-relative instruction in first %d bytes (base+0x%llX)",
            hookSize, (unsigned long long)(func - g_gameBase));
        return false;
    }
    uint8_t* trampoline = (uint8_t*)VirtualAlloc(nullptr, 64, MEM_COMMIT|MEM_RESERVE, PAGE_EXECUTE_READWRITE);
    if (!trampoline) return false;
    memcpy(trampoline, orig, hookSize);
    trampoline[hookSize    ] = 0xFF; trampoline[hookSize + 1] = 0x25;
    *(uint32_t*)(trampoline + hookSize + 2) = 0;
    *(uintptr_t*)(trampoline + hookSize + 6) = func + hookSize;
    g_origCanShow = (PFN_CanShow)trampoline;
    DWORD op;
    VirtualProtect((void*)func, hookSize, PAGE_EXECUTE_READWRITE, &op);
    uint8_t* p = (uint8_t*)func;
    p[0] = 0xFF; p[1] = 0x25;
    *(uint32_t*)(p + 2) = 0;
    *(uintptr_t*)(p + 6) = (uintptr_t)&HookedCanShow;
    for (int i = 14; i < hookSize; i++) p[i] = 0x90; // NOP-pad tail of replaced instructions
    VirtualProtect((void*)func, hookSize, op, &op);
    FlushInstructionCache(GetCurrentProcess(), (void*)func, hookSize);
    // Capacity check already gated above; recording here is unconditional.
    g_hookTable[g_hookCount].addr = func;
    g_hookTable[g_hookCount].size = hookSize;
    memcpy(g_hookTable[g_hookCount].orig, orig, hookSize);
    g_hookCount++;
    Log("HOOK CanShow: OK base+0x%llX (size=%d)", (unsigned long long)(func - g_gameBase), hookSize);
    return true;
}

// ============================================================
//  Menu request — the CD 2.01.00 open/close path
// ============================================================
// Locate MenuRequest + the menu object chain. Anchor: the game's own
// "is this view open" test, which reads a byte, ANDs 0x60 and compares 0x40:
//
//     movzx eax, byte [rax + STATE]     0F B6 80 <disp32>
//     and   al, 0x60                    24 60
//     cmp   al, 0x40                    3C 40
//     ...
//     mov   rcx, [rip + GLOBAL]         48 8B 0D <disp32>
//     mov   rcx, [rcx + OBJOFF]         48 8B 89 <disp32>
//     call  MENUREQUEST                 E8 <rel32>
//
// The global and the member offset must be unanimous across every match; the
// function itself is taken by majority (build 25116796: 3 sites, all agreeing
// on the global and +0x98, and 2 of 3 on the function).
static bool ResolveMenuRequest() {
    uint8_t* base = (uint8_t*)g_gameBase;
    uintptr_t glob = 0; uint32_t objOff = 0;
    bool globConflict = false;
    uintptr_t fnCand[8] = {}; int fnVotes[8] = {}; int nFn = 0;
    int matches = 0;

    for (DWORD i = 0; (size_t)i + 0x80 < g_imageSize; i++) {
        if (base[i] != 0x0F || base[i+1] != 0xB6 || base[i+2] != 0x80) continue;
        if (base[i+7] != 0x24 || base[i+8] != 0x60)  continue;
        if (base[i+9] != 0x3C || base[i+10] != 0x40) continue;

        for (int f = 11; f < 0x60; f++) {
            uint8_t* q = base + i + f;
            if (q[0] != 0x48 || q[1] != 0x8B || q[2] != 0x89) continue;
            uint32_t oo = *(uint32_t*)(q + 3);
            if (oo < 0x10 || oo > 0x2000) break;

            uintptr_t g = 0;
            for (int back = 7; back <= 0x20; back++) {
                uint8_t* r = q - back;
                if (r[0] == 0x48 && r[1] == 0x8B && r[2] == 0x0D) {
                    uintptr_t c = (uintptr_t)(r + 7) + *(int32_t*)(r + 3);
                    if (c > g_gameBase && c < g_gameBase + g_imageSize) g = c;
                }
            }
            uintptr_t tgt = 0;
            for (int f2 = 7; f2 < 0x20; f2++) {
                uint8_t* r = q + f2;
                if (r[0] != 0xE8) continue;
                uintptr_t t = (uintptr_t)(r + 5) + *(int32_t*)(r + 1);
                if (t > g_gameBase && t < g_gameBase + g_imageSize) tgt = t;
                break;
            }
            if (!g || !tgt) break;

            matches++;
            if (!glob) { glob = g; objOff = oo; }
            else if (glob != g || objOff != oo) globConflict = true;

            int k = 0;
            for (; k < nFn; k++) if (fnCand[k] == tgt) { fnVotes[k]++; break; }
            if (k == nFn && nFn < 8) { fnCand[nFn] = tgt; fnVotes[nFn] = 1; nFn++; }
            break;
        }
    }

    if (!glob || globConflict || !nFn) {
        Log("MenuRequest: FAIL (%d match(es), conflict=%d)", matches, (int)globConflict);
        return false;
    }
    uintptr_t best = 0; int bestVotes = 0;
    for (int k = 0; k < nFn; k++)
        if (fnVotes[k] > bestVotes) { bestVotes = fnVotes[k]; best = fnCand[k]; }

    g_menuRequestFn  = best;
    g_menuRootGlobal = glob;
    g_menuObjOff     = objOff;
    Log("MenuRequest: OK fn=base+0x%llX  menuObj=*(*(base+0x%llX)+0x%X)  (%d sites, %d votes)",
        (unsigned long long)(best - g_gameBase),
        (unsigned long long)(glob - g_gameBase), objOff, matches, bestVotes);
    return true;
}

// Which screen id makes ModeSwitcher emit the "store" view tag. ModeSwitcher
// dispatches through jump tables whose slots are image-base-relative; find the
// table whose case block linearly contains the single LEA of "store".
static int32_t ResolveStoreScreenId() {
    if (!g_fnModeSwitcher) return -1;
    const uint32_t WIN = 0x1200;
    uint8_t* fn = (uint8_t*)g_fnModeSwitcher;

    uintptr_t strStore = FindString("store");
    if (!strStore) return -1;
    uintptr_t storeLea = 0; int storeHits = 0;
    for (uint32_t i = 0; i + 7 <= WIN; i++) {
        uint8_t* p = fn + i;
        if ((p[0] == 0x48 || p[0] == 0x4C) && p[1] == 0x8D && (p[2] & 0xC7) == 0x05) {
            if ((uintptr_t)(p + 7) + *(int32_t*)(p + 3) == strStore) {
                storeLea = (uintptr_t)p; storeHits++;
            }
        }
    }
    if (storeHits != 1) {
        Log("StoreScreenId: 'store' LEA ambiguous inside ModeSwitcher (%d hits)", storeHits);
        return -1;
    }

    // Every  MOV r32,[reg + reg*4 + disp32]  is a candidate dispatch. Collect
    // ALL of their table addresses FIRST: ModeSwitcher has an outer switch (the
    // mode) and an inner one (the screen), and the two tables sit back to back
    // in memory. Reading a table until a slot falls outside the function body
    // therefore runs straight through the boundary and merges both tables --
    // which reports the store case at outer_count + inner_index (12 = 7 + 5 on
    // build 25116796) instead of the index the game actually dispatches on.
    // Bounding each table by the next table start fixes that.
    uintptr_t bestTable = 0, bestWidth = (uintptr_t)-1;
    int bestCase = -1, bestCount = 0;

    uintptr_t tables[16]; int nTables = 0;
    for (uint32_t i = 0; i + 7 <= WIN && nTables < 16; i++) {
        uint8_t* p = fn + i;
        if (p[0] != 0x8B || (p[1] & 0xC7) != 0x84) continue;
        uintptr_t t = g_gameBase + *(uint32_t*)(p + 3);
        bool dup = false;
        for (int k = 0; k < nTables; k++) if (tables[k] == t) { dup = true; break; }
        if (!dup) tables[nTables++] = t;
    }

    for (int ti = 0; ti < nTables; ti++) {
        uintptr_t tableVA = tables[ti];
        // Nearest other table that starts after this one bounds its length.
        uintptr_t bound = tableVA + 0x40 * 4;
        for (int k = 0; k < nTables; k++)
            if (tables[k] > tableVA && tables[k] < bound) bound = tables[k];

        uintptr_t lo = g_fnModeSwitcher, hi = g_fnModeSwitcher + WIN;
        uintptr_t tgts[0x41]; int n = 0;
        __try {
            for (; n < 0x40 && tableVA + n * 4 < bound; n++) {
                uintptr_t t = g_gameBase + *(uint32_t*)(tableVA + n * 4);
                if (t < lo || t >= hi) break;
                tgts[n] = t;
            }
        } __except(EXCEPTION_EXECUTE_HANDLER) { continue; }
        if (n < 4) continue;

        for (int k = 0; k < n; k++) {
            uintptr_t nextB = hi;
            for (int j = 0; j < n; j++)
                if (tgts[j] > tgts[k] && tgts[j] < nextB) nextB = tgts[j];
            if (tgts[k] <= storeLea && storeLea < nextB) {
                // Keep the NARROWEST containing block. ModeSwitcher nests two
                // switches: the outer one on the mode, the inner one on the
                // screen. The outer case for "ingame-global" spans the whole
                // inner switch, so it also contains the "store" LEA -- taking
                // the first match returns the mode (4) instead of the screen
                // (5), and the game then opens a different screen entirely.
                // The innermost range is the specific case.
                uintptr_t width = nextB - tgts[k];
                if (width < bestWidth) {
                    bestWidth = width;
                    bestCase  = k;
                    bestTable = tableVA;
                    bestCount = n;
                }
            }
        }
    }

    if (bestCase >= 0) {
        Log("StoreScreenId: %d (table base+0x%llX, %d cases, narrowest block 0x%llX, "
            "'store' at ModeSwitcher+0x%llX)",
            bestCase, (unsigned long long)(bestTable - g_gameBase), bestCount,
            (unsigned long long)bestWidth,
            (unsigned long long)(storeLea - g_fnModeSwitcher));
        return bestCase;
    }
    Log("StoreScreenId: no dispatch table covers the 'store' case");
    return -1;
}

// ---- game-menu gate --------------------------------------------------------
// The first  MOV reg,[RCX+disp32]  loads with a struct-sized displacement in a
// code window, in address order (used on FindPanelTop's prolog).
static int CollectRcxDisp32Loads(const uint8_t* f, int len, uint32_t* out, int n, int max) {
    __try {
        for (int i = 0; i + 6 < len && n < max; i++) {
            int k = i;
            if (f[k] == 0x48 || f[k] == 0x4C || f[k] == 0x49 || f[k] == 0x4D) k++;
            if (f[k] != 0x8B || (f[k+1] & 0xC7) != 0x81) continue;
            uint32_t disp = *(const uint32_t*)(f + k + 2);
            if (disp < 0x1000 || disp > 0x100000) continue;
            bool dup = false;
            for (int j = 0; j < n; j++) if (out[j] == disp) dup = true;
            if (!dup) out[n++] = disp;
            i = k + 5;
        }
    } __except(EXCEPTION_EXECUTE_HANDLER) {}
    return n;
}

// FindPanelTop is the most-voted callee of the first CALL within 40 bytes of a
// LEA RDX,[MainMenuView2] (build 25116796: 21/21 sites). Its prolog loads the
// panel entry array and count from pm (two MOV reg,[RCX+disp32]); the view
// state offset is the majority disp32 of the open-test idiom
// MOVZX EAX,byte [RAX+disp32]; AND AL,0x60; CMP AL,0x40 (98 sites, +0xB0).
static bool ResolvePanelLookup() {
    uint8_t* base = (uint8_t*)g_gameBase;
    // 1) state byte offset
    {
        uint32_t cand[8] = {}; int votes[8] = {}; int nc = 0;
        for (DWORD i = 0; (size_t)i + 11 < g_imageSize; i++) {
            if (base[i] != 0x0F || base[i+1] != 0xB6 || base[i+2] != 0x80) continue;
            if (base[i+7] != 0x24 || base[i+8] != 0x60) continue;
            if (base[i+9] != 0x3C || base[i+10] != 0x40) continue;
            uint32_t off = *(uint32_t*)(base + i + 3);
            if (off < 0x10 || off > 0x2000) continue;
            int k = 0;
            for (; k < nc; k++) if (cand[k] == off) { votes[k]++; break; }
            if (k == nc && nc < 8) { cand[nc] = off; votes[nc] = 1; nc++; }
        }
        int best = 0;
        for (int k = 0; k < nc; k++) if (votes[k] > best) { best = votes[k]; g_panelStateOff = cand[k]; }
    }
    // 2) FindPanelTop
    uintptr_t strMM = FindString("MainMenuView2");
    if (!strMM) { Log("PanelLookup:  FAIL (MainMenuView2 string missing)"); return false; }
    uintptr_t cand[16] = {}; int votes[16] = {}; int nc = 0;
    uintptr_t lea = 0;
    for (int guard = 0; guard < 64; guard++) {
        lea = FindLEA(strMM, lea ? lea + 1 : 0);
        if (!lea) break;
        uint8_t* p = (uint8_t*)lea;
        if (!(p[0] == 0x48 && p[1] == 0x8D && p[2] == 0x15)) continue;     // LEA RDX only
        uintptr_t t = 0;
        for (int j = 7; j < 40; j++) {
            if (p[j] != 0xE8) continue;
            t = (uintptr_t)(p + j + 5) + *(int32_t*)(p + j + 1);
            if (t <= g_gameBase || t >= g_gameBase + g_imageSize) t = 0;
            break;
        }
        if (!t) continue;
        int k = 0;
        for (; k < nc; k++) if (cand[k] == t) { votes[k]++; break; }
        if (k == nc && nc < 16) { cand[nc] = t; votes[nc] = 1; nc++; }
    }
    int best = 0, total = 0; uintptr_t fn = 0;
    for (int k = 0; k < nc; k++) { total += votes[k]; if (votes[k] > best) { best = votes[k]; fn = cand[k]; } }
    if (!fn || best < 3 || best * 2 <= total) {
        Log("PanelLookup:  FAIL (FindPanelTop best %d/%d)", best, total); return false;
    }
    // 3) pm offsets from FindPanelTop's prolog: first two MOV reg,[RCX+disp32].
    //    Another mod (QuickMenuHotkeys seeds pm the same way) may already have
    //    its JMP on the prolog; the stolen bytes then live in ITS trampoline,
    //    so read them from there and continue behind the 14-byte JMP.
    uint32_t found[2] = {}; int n = 0;
    const uint8_t* f = (const uint8_t*)fn;
    if (f[0] == 0xFF && f[1] == 0x25 && *(const int32_t*)(f + 2) == 0) {
        const uint8_t* tramp = *(const uint8_t* const*)(f + 6);
        n = CollectRcxDisp32Loads(tramp, 0x100, found, n, 2);
        n = CollectRcxDisp32Loads(f + 14, 0x40 - 14, found, n, 2);
        Log("PanelLookup:  FindPanelTop already hooked by another mod — prolog read via its trampoline");
    } else {
        n = CollectRcxDisp32Loads(f, 0x40, found, n, 2);
    }
    if (n < 2 || !g_panelStateOff) {
        Log("PanelLookup:  FAIL (prolog offsets %d, state off 0x%X)", n, g_panelStateOff); return false;
    }
    g_fnFindPanelTop = fn; g_pmArrayOff = found[0]; g_pmCountOff = found[1];
    Log("PanelLookup:  OK FindPanelTop=base+0x%llX (%d/%d votes) pm array +0x%X count +0x%X state byte +0x%X",
        (unsigned long long)(fn - g_gameBase), best, total, g_pmArrayOff, g_pmCountOff, g_panelStateOff);
    return true;
}

// Read-only capture of the panel manager: FindPanelTop(pm, name) is called
// from hundreds of UI sites long before any hotkey, so pm is known within the
// first frames. The candidate is validated against the array the function
// itself walks; a wrong RCX is never adopted.
extern "C" void __fastcall CaptureOnFindPanelTop(void* rcx, void*, void*, void*) {
    if (InterlockedCompareExchange64(&g_panelManager, 0, 0) != 0) return;
    uintptr_t pm = (uintptr_t)rcx;
    if (pm <= 0x10000 || pm >= 0x7FFFFFFFFFFFULL || !g_pmArrayOff) return;
    __try {
        uintptr_t entries = *(uintptr_t*)(pm + g_pmArrayOff);
        uint32_t  count   = *(uint32_t*)(pm + g_pmCountOff);
        if (entries <= 0x10000 || count == 0 || count > 0x1000) return;
        if (InterlockedCompareExchange64(&g_panelManager, (LONG64)pm, 0) == 0)
            Log("PanelManager: 0x%llX captured from FindPanelTop (entries=0x%llX count=%u)",
                (unsigned long long)pm, (unsigned long long)entries, count);
    } __except(EXCEPTION_EXECUTE_HANDLER) {}
}

// Is the named view on screen right now? false also when the gate is unavailable.
static bool IsViewOpen(const char* name, uint8_t* stOut = nullptr) {
    if (!g_fnFindPanelTop || !g_panelStateOff) return false;
    uintptr_t pm = (uintptr_t)InterlockedCompareExchange64(&g_panelManager, 0, 0);
    if (!pm) return false;
    typedef uintptr_t (__fastcall* FindPanelTopFn)(uintptr_t, const char*);
    __try {
        uintptr_t panel = ((FindPanelTopFn)g_fnFindPanelTop)(pm, name);
        if (!panel) return false;
        uint8_t st = *(uint8_t*)(panel + g_panelStateOff);
        if (stOut) *stOut = st;
        return (st & 0x60) == 0x40;
    } __except(EXCEPTION_EXECUTE_HANDLER) {}
    return false;
}

// Push a screen open/close request through the game's own queue.
static bool MenuRequestScreen(int32_t screenId, bool open) {
    if (!g_menuRequestFn || !g_menuRootGlobal || screenId < 0) return false;
    typedef void (__fastcall* MenuRequestFn)(uintptr_t, uint8_t, uint8_t);
    __try {
        uintptr_t root = *(uintptr_t*)g_menuRootGlobal;
        if (root <= 0x10000) { Log("  MenuRequest: root global null"); return false; }
        uintptr_t obj = *(uintptr_t*)(root + g_menuObjOff);
        if (obj <= 0x10000) { Log("  MenuRequest: menu object null"); return false; }
        ((MenuRequestFn)g_menuRequestFn)(obj, (uint8_t)screenId, open ? 1 : 0);
        Log("  MenuRequest(screen=%d, open=%d) sent", screenId, (int)open);
        return true;
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        Log("  MenuRequest: EXCEPTION (screen=%d open=%d)", screenId, (int)open);
    }
    return false;
}

static int32_t EffectiveStoreScreenId() {
    return (g_storeScreenIdIni >= 0) ? g_storeScreenIdIni : g_storeScreenId;
}

// Mount / unmount the warehouse view through the game's own request queue.
// Returns false when the request could not be sent, in which case the panel
// cannot render and the caller must roll the open back.
static bool TriggerWarehouseViewMount() {
    if (MenuRequestScreen(EffectiveStoreScreenId(), true)) return true;
    Log("  ViewMount: menu request unavailable (fn=%d screen=%d)",
        g_menuRequestFn ? 1 : 0, EffectiveStoreScreenId());
    return false;
}

static void TriggerWarehouseViewUnmount() {
    if (!MenuRequestScreen(EffectiveStoreScreenId(), false))
        Log("  ViewUnmount: menu request unavailable");
}

// ============================================================
//  Warehouse panel initialisation (everything that needs the handler)
//  Called from HookedCanShow / CaptureOnHandler right after the controller
//  is captured, or via WM_INIT_WAREHOUSE when it was already known.
// ============================================================
static void InitWarehousePanel(uintptr_t handler, const char* initString) {
    // Make sure the housing records are at their maximum before the panel reads
    // them. A no-op once the boot-time worker has done its job; it only matters
    // when the manager was re-created after that (e.g. a second save loaded).
    PatchSlotsViaManager();

    // Ask for the view mount again now that the handler exists. TriggerWarehouse
    // already sent one request before the capture; the second one is part of the
    // sequence that was confirmed in-game and is kept as is.
    TriggerWarehouseViewMount();

    // Empty 0x15 ("prepare") before 0x0E, the order of a natural open. The 0x15
    // dispatcher makes three virtual calls on the sub-objects at g_offPrepare1/2/3
    // before it iterates sub-commands; with count=0 only those calls run. All
    // three sub-objects must be non-null or the dispatcher crashes.
    if (g_fnHandler) {
        __try {
            uintptr_t sub1 = *(uintptr_t*)(handler + g_offPrepare1);
            uintptr_t sub2 = *(uintptr_t*)(handler + g_offPrepare2);
            uintptr_t sub3 = *(uintptr_t*)(handler + g_offPrepare3);
            if (sub1 > 0x10000 && sub2 > 0x10000 && sub3 > 0x10000) {
                uint8_t emptyPacket[24] = {};
                emptyPacket[0] = 0x15;
                typedef void (__fastcall *PFN_Handler)(void*, void*, void*, void*);
                ((PFN_Handler)g_fnHandler)((void*)handler, nullptr, nullptr, (void*)emptyPacket);
                Log("  Empty 0x15 sent (prepare calls triggered, offs=%X/%X/%X)",
                    g_offPrepare1, g_offPrepare2, g_offPrepare3);
            } else {
                Log("  Empty 0x15 SKIPPED (sub-objects null: %llX/%llX/%llX at offs %X/%X/%X)",
                    (unsigned long long)sub1, (unsigned long long)sub2,
                    (unsigned long long)sub3,
                    g_offPrepare1, g_offPrepare2, g_offPrepare3);
            }
        } __except(EXCEPTION_EXECUTE_HANDLER) {
            Log("  Empty 0x15 EXCEPTION");
        }
    }

    // Now send cmd 0x0E — sets active flag + tells panel-manager to show.
    if (g_fnHandler) {
        __try {
            uint8_t showPacket[24] = {};
            showPacket[0] = 0x0E;
            typedef void (__fastcall *PFN_Handler)(void*, void*, void*, void*);
            ((PFN_Handler)g_fnHandler)((void*)handler, nullptr, nullptr, (void*)showPacket);
            Log("  Cmd 0x0E sent");
        } __except(EXCEPTION_EXECUTE_HANDLER) {
            Log("  Cmd 0x0E EXCEPTION — falling back to manual active-flag set");
            __try {
                *(uint8_t*)(handler + g_offActiveFlag) = 1;
            } __except(EXCEPTION_EXECUTE_HANDLER) {}
        }
    }

    // Reset faction-donation state (3 shorts, 0xFFFF = no faction selected).
    if (g_offDonationState) {
        __try {
            uint16_t* ds = (uint16_t*)(handler + g_offDonationState);
            if (ds[0] != 0xFFFF || ds[1] != 0xFFFF || ds[2] != 0xFFFF) {
                ds[0] = 0xFFFF;
                ds[1] = 0xFFFF;
                ds[2] = 0xFFFF;
                Log("  Cleared donation state at +0x%X", g_offDonationState);
            }
        } __except(EXCEPTION_EXECUTE_HANDLER) {}
    }

    // Save the original PanelValue slot content before the first mod write; it
    // is restored on close. A canonical pointer in this slot means the offset
    // drifted to another field, and the override is disabled for the session.
    if (InterlockedCompareExchange64(&g_savedPanelValueSlot, 0, 0) == -1) {
        __try {
            uintptr_t orig = *(uintptr_t*)(handler + g_offPanelValue);
            InterlockedExchange64(&g_savedPanelValueSlot, (LONG64)orig);
            // PanelValue is a small type-id scalar. A canonical pointer here means
            // the slot drifted to a different field — disable override/restore.
            g_panelValueSlotValid = (orig < 0x10000);
            Log("  Saved original handler+0x%X = 0x%llX (PanelValue slot%s)",
                g_offPanelValue, (unsigned long long)orig,
                g_panelValueSlotValid ? "" : " — looks relocated, override disabled");
        } __except(EXCEPTION_EXECUTE_HANDLER) {}
    }

    // Write the PanelValue for the active panel (see g_panelValueCfg), then make
    // sure the live capacity of the chest being opened is at its maximum.
    {
        LONG act = InterlockedCompareExchange(&g_activePanel, 0, 0);
        if (act < 0 || act >= PANEL_COUNT) act = PANEL_PRIVATE;
        LONG pv  = 0;
        const char* src = "none";
        pv = InterlockedCompareExchange(&g_panelValueCfg[act], 0, 0);
        if (pv) {
            src = "INI per-panel";
        } else if (act == PANEL_PRIVATE) {
            pv = InterlockedCompareExchange(&g_privatePanelValueCfg, 0, 0);
            src = "INI";
        } else {
            pv = InterlockedCompareExchange(&g_gatherablesPanelValueCfg, 0, 0);
            src = "default (GatherablesPanelValue)";
        }
        if (pv != 0 && g_panelValueSlotValid) {
            __try {
                *(uintptr_t*)(handler + g_offPanelValue) = (uintptr_t)pv;
                Log("  PanelValue override: handler+0x%X = 0x%llX (%s, source=%s)",
                    g_offPanelValue, (unsigned long long)(uintptr_t)pv,
                    g_panels[act].name, src);
            } __except(EXCEPTION_EXECUTE_HANDLER) {
                Log("  PanelValue override EXCEPTION");
            }
        } else if (pv != 0 && !g_panelValueSlotValid) {
            Log("  PanelValue override SKIPPED (slot +0x%X looks relocated)", g_offPanelValue);
        }

        // Live capacity check for the chest being opened. PatchGroupCapacities
        // only ever touches the five housing groups; the record was raised at
        // boot and the game normally seeds the groups at 1000 itself, so this is
        // the safety net for a save that loaded before the record patch ran.
        {
            static const uint16_t kFileId[PANEL_COUNT] = {
                0x08, 0x13, 0x0F, 0x10, 0x11, 0x12   // Private, Gatherables, Dresser, Fridge, Symbol, Collecting
            };
            uint16_t rtId = RuntimeIndexForFileId(kFileId[act]);
            Log("  record slots for %s (file id 0x%02X -> runtime 0x%02X) = %d",
                g_panels[act].name, kFileId[act], rtId, ReadChestSlots(rtId));
            int r = PatchGroupCapacities(rtId);
            if (r) Log("  InvGroups: %d live group(s) raised", r);
        }
    }

    // Bind the inventory channels. SetInventory tokenises the string by ';' and
    // ',' and per token subscribes (",True") or unsubscribes (",False") the
    // channel on the matching sub-controller. Subscriptions accumulate, so the
    // previously bound panel must be unbound explicitly, and the current one is
    // unbound+rebound to force a refresh — the order a natural chest open uses.
    if (g_fnSetInventory && initString && *initString) {
        typedef void (__fastcall *PFN_SetInv)(void*, void*);
        auto buildUnbind = [](const char* src, char* dst, size_t dstSize) {
            if (!src || !*src) { dst[0] = 0; return; }
            strncpy(dst, src, dstSize - 1);
            dst[dstSize - 1] = 0;
            for (char* p = dst; *p; p++) {
                if ((p[0] == ',' || p[0] == ';') &&
                    (p[1] == 'T' || p[1] == 't') &&
                    (p[2] == 'R' || p[2] == 'r') &&
                    (p[3] == 'U' || p[3] == 'u') &&
                    (p[4] == 'E' || p[4] == 'e')) {
                    p[1] = 'F'; p[2] = 'a'; p[3] = 'l'; p[4] = 's';
                    size_t len = strlen(p + 5);
                    if (len + 6 < dstSize - (size_t)(p - dst)) {
                        memmove(p + 6, p + 5, len + 1);
                        p[5] = 'e';
                        p += 5;
                    }
                }
            }
        };

        // Append ",Default" (the warehouse's CategoryType attribute, token[0] of
        // the game's category-type table) to each ';'-separated bind segment.
        // This makes SetInventory take its 4-field branch, which runs the game's
        // own category populate+render pair on each sub-widget — what a natural
        // NPC open does via the widget Init. The item binding is identical in
        // the 3- and 4-field branches, so this only ADDS the category tab bar.
        // Only the BIND (True) string gets the 4th field; unbind stays 3-field.
        auto buildBind = [](const char* src, char* dst, size_t dstSize) {
            dst[0] = 0;
            if (!src || !*src) return;
            size_t o = 0;
            const char* seg = src;
            while (*seg) {
                const char* semi = strchr(seg, ';');
                int segLen = semi ? (int)(semi - seg) : (int)strlen(seg);
                int n = _snprintf_s(dst + o, dstSize - o, _TRUNCATE, "%.*s,Default%s",
                                    segLen, seg, semi ? ";" : "");
                if (n <= 0) { dst[0] = 0; return; }   // overflow → caller falls back to 3-field
                o += n;
                if (!semi) break;
                seg = semi + 1;
            }
        };
        char bindStr[320] = {};
        buildBind(initString, bindStr, sizeof(bindStr));
        const char* bindArg = bindStr[0] ? bindStr : initString;

        char curUnbind[256] = {};
        buildUnbind(initString, curUnbind, sizeof(curUnbind));

        LONG curBound = InterlockedCompareExchange(&g_currentBoundPanel, 0, 0);
        LONG ap = InterlockedCompareExchange(&g_activePanel, 0, 0);
        if (ap < 0 || ap >= PANEL_COUNT) ap = PANEL_PRIVATE;

        // Step 1: unbind the previously bound panel (if different from current).
        if (curBound >= 0 && curBound < PANEL_COUNT && curBound != ap) {
            char prevUnbind[256] = {};
            buildUnbind(g_panels[curBound].initString, prevUnbind, sizeof(prevUnbind));
            if (prevUnbind[0]) {
                __try {
                    ((PFN_SetInv)g_fnSetInventory)((void*)handler, (void*)prevUnbind);
                    Log("  SetInventory unbind PREV (%s, \"%s\")",
                        g_panels[curBound].name, prevUnbind);
                } __except(EXCEPTION_EXECUTE_HANDLER) {
                    Log("  SetInventory unbind PREV EXCEPTION");
                }
            }
        }

        // Step 2: unbind+rebind of the current panel (forces a refresh).
        __try {
            if (curUnbind[0]) {
                ((PFN_SetInv)g_fnSetInventory)((void*)handler, (void*)curUnbind);
                Log("  SetInventory unbind CUR  (\"%s\")", curUnbind);
            }
            ((PFN_SetInv)g_fnSetInventory)((void*)handler, (void*)bindArg);
            Log("  SetInventory bind   CUR  (\"%s\")", bindArg);
            InterlockedExchange(&g_currentBoundPanel, ap);
        } __except(EXCEPTION_EXECUTE_HANDLER) {
            Log("  SetInventory EXCEPTION (string=\"%s\")", initString);
        }

    }

    // Fix bottom inventory label + top title
    if (g_fnSetTitle) {
        typedef uint8_t (__fastcall *PFN_SetTitle)(uintptr_t, const char*);
        PFN_SetTitle setTitle = (PFN_SetTitle)g_fnSetTitle;
        const char* title = GetWarehouseTitle();
        {
            LONG ap = InterlockedCompareExchange(&g_activePanel, 0, 0);
            if (ap < 0 || ap >= PANEL_COUNT) ap = PANEL_PRIVATE;
            Log("  Title selected: \"%s\" (active=%s)", title, g_panels[ap].name);
        }

        __try {
            uintptr_t bottomLabel = *(uintptr_t*)(handler + g_offBottomLabel);
            if (bottomLabel > 0x10000 && bottomLabel < 0x7FFFFFFFFFFF) {
                setTitle(bottomLabel, title);
                Log("  Bottom label (+0x%X) set: lang=%d", g_offBottomLabel, GetGameLanguage());
            } else {
                Log("  Bottom label (+0x%X) invalid pointer", g_offBottomLabel);
            }
        } __except(EXCEPTION_EXECUTE_HANDLER) {
            Log("  Bottom label (+0x%X) EXCEPTION", g_offBottomLabel);
        }

        __try {
            uintptr_t topNode = g_offTopTitle ? *(uintptr_t*)(handler + g_offTopTitle) : 0;
            bool topPtrOk = topNode > 0x10000 && topNode < 0x7FFFFFFFFFFF;
            // The slot must hold a UI node: its vtable has to live inside the
            // game image. Anything else means the base-class layout moved.
            uintptr_t topVt = topPtrOk ? *(uintptr_t*)topNode : 0;
            bool topIsNode = topVt >= g_gameBase && topVt < g_gameBase + g_imageSize;
            if (topPtrOk && !topIsNode) {
                Log("  Top title (+0x%X) skipped: 0x%llX has no in-image vtable (0x%llX)",
                    g_offTopTitle, (unsigned long long)topNode, (unsigned long long)topVt);
            } else if (topPtrOk) {
                uint8_t ret = setTitle(topNode, title);
                Log("  Top title (+0x%X) set: lang=%d ret=%u (node vtable base+0x%llX)",
                    g_offTopTitle, GetGameLanguage(), (unsigned)ret,
                    (unsigned long long)(topVt - g_gameBase));
            } else if (!g_offTopTitle) {
                Log("  Top title: no offset resolved this build — skipped");
            } else {
                Log("  Top title (+0x%X) slot empty — left at the game's default", g_offTopTitle);
            }
        } __except(EXCEPTION_EXECUTE_HANDLER) {
            Log("  Top title (+0x%X) EXCEPTION", g_offTopTitle);
        }
    }

    LogModalState("  InitWarehousePanel done");
}

// ============================================================
//  F6 / Controller: Toggle Warehouse
// ============================================================
// ClearActivePanelState: clears the controller's active flag and restores the
// PanelValue slot. Does NOT touch g_warehouseActive — the caller decides.
static void ClearActivePanelState(uintptr_t handler) {
    if (!handler) return;
    LONG ap = InterlockedCompareExchange(&g_activePanel, 0, 0);
    const char* apName = (ap >= 0 && ap < PANEL_COUNT) ? g_panels[ap].name : "?";
    __try {
        *(uint8_t*)(handler + g_offActiveFlag) = 0;
        LONG64 saved = InterlockedCompareExchange64(&g_savedPanelValueSlot, 0, 0);
        if (saved != -1 && g_panelValueSlotValid)
            *(uint64_t*)(handler + g_offPanelValue) = (uint64_t)saved;
        Log("  Panel [%s] hidden (active flag cleared, PanelValue restored)", apName);
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        Log("  Panel [%s] hide EXCEPTION", apName);
    }
}

// triggerKind: 0 = open, 1 = close (modal-aware, used by F-keys),
//              2 = force close (skip the modal block — used by controller
//              B/Circle and per-panel buttons, which handle the modal case
//              themselves at press time).
static void TriggerWarehouse(int triggerKind = 0) {
    bool forceClose = (triggerKind == 2);
    // mainChar only serves as the "a session is loaded" gate here.
    if (!InterlockedCompareExchange64(&g_mainChar, 0, 0)) { Log("NOT READY: mainChar"); return; }

    if (!InterlockedCompareExchange(&g_warehouseActive, 0, 0)) {
        // Re-open cooldown: when DualSense is mapped through Steam Input,
        // pressing Circle fires both the HID-Circle path AND the XInput-B
        // path. Each path posts its own WM_TRIGGER_WAREHOUSE, so the close
        // is followed by a second toggle that would re-open instantly.
        // Block any open request within 250ms of a close to absorb that
        // second message (and any other near-simultaneous controller
        // duplication).
        ULONGLONG now = GetTickCount64();
        ULONGLONG closedAt = g_closeTimestamp;
        if (closedAt && now - closedAt < 250) {
            Log("BLOCKED: re-open within %llu ms of close (cooldown)",
                (unsigned long long)(now - closedAt));
            return;
        }

        // Game-menu gate: never open on top of the main menu (inventory, quest
        // journal, skills, ...) or the world map — the request would close
        // that menu and mount the warehouse over it.
        {
            static const char* const kViews[] = { "MainMenuView2", "WorldMapView" };
            for (int v = 0; v < 2; v++) {
                uint8_t st = 0;
                if (IsViewOpen(kViews[v], &st)) {
                    Log("BLOCKED: %s is open (state 0x%02X) — close it first", kViews[v], st);
                    InterlockedExchange(&g_nextOpenPanel, PANEL_PRIVATE);
                    return;
                }
            }
        }

        LONG targetPanel = InterlockedExchange(&g_nextOpenPanel, PANEL_PRIVATE);
        {
            LONG tp = targetPanel;
            if (tp < 0 || tp >= PANEL_COUNT) tp = PANEL_PRIVATE;
            Log("=== OPENING WAREHOUSE (%s) ===", g_panels[tp].name);
        }
        InterlockedExchange(&g_activePanel, targetPanel);
        InterlockedExchange(&g_warehouseActive, 1);

        // The panel is initialised once the controller is known. On the first
        // open of a session the handler is usually still NULL here — the game
        // creates it after the view mounts and HookedCanShow captures it on the
        // game thread — so the init is always deferred: InputThread posts
        // WM_INIT_WAREHOUSE once g_handlerThis is set, and the capture paths run
        // InitWarehousePanel inline when a press is pending.
        InterlockedExchange(&g_initRetryCount, 0);
        InterlockedExchange(&g_initPending, 1);

        // Mount the view now, independent of the handler capture.
        if (!TriggerWarehouseViewMount()) {
            Log("  OPEN ABORTED: view mount failed — rolled back");
            InterlockedExchange(&g_initPending, 0);
            InterlockedExchange(&g_warehouseActive, 0);
            InterlockedExchange(&g_activePanel, PANEL_PRIVATE);
            return;
        }

    } else {
        // Block close while a modal dialog is up — but only for non-forced
        // closes (hotkeys). Controller closes always proceed.
        if (!forceClose && IsNewModalDialogVisible()) {
            Log("CLOSE BLOCKED: modal dialog still open");
            return;
        }
        Log("=== CLOSING WAREHOUSE ===");
        InterlockedExchange(&g_warehouseActive, 0);
        InterlockedExchange(&g_initPending, 0);
        // Clear any in-flight controller pending-close flags so a stray
        // release after this close doesn't trigger an immediate re-open.
        InterlockedExchange(&g_pendingBClose, 0);
        InterlockedExchange(&g_pendingCircleClose, 0);
        // Stamp close time for the re-open cooldown (see open branch).
        g_closeTimestamp = GetTickCount64();

        // Clear the controller's own state.
        ClearActivePanelState((uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0));

        // Hand the menu layer back to the game.
        TriggerWarehouseViewUnmount();

        // Reset so the next legacy single-hotkey press opens Private.
        InterlockedExchange(&g_activePanel, PANEL_PRIVATE);
        // NOTE: do NOT reset g_currentBoundPanel here. SetInventory subscribes
        // accumulate on the sub-controllers (sub+0x218 = channelId) until an
        // explicit ",False" unsub is sent for that exact channel. We need to
        // remember which panel's channels are currently subscribed so the next
        // open can unbind them via the "unbind PREV" path. Resetting to -1
        // skips that unbind and leaves the previous panel's channels active —
        // which is why F7+ after F6-Private kept showing Private's items.

        Log("  Warehouse closed");

        // Modal popup state belongs to the closed warehouse — clear so a
        // stuck flag doesn't survive into the next session.
        InterlockedExchange(&g_itemDetailActiveCount, 0);
        InterlockedExchange(&g_modalDismissed, 0);

        // Force-close fallback for housing chests: ClearActivePanelState
        // works for Private (Camp panel) but doesn't always visually close
        // Gatherables / Refrigerator / Dresser / Symbol / Collecting. The
        // game's native ESC handler does additional sub-state cleanup we
        // can't replicate. Send a synthetic VK_ESCAPE through the original
        // WndProc so the game performs that cleanup. Safe here because:
        //   - we're already on the game thread (PostMessage dispatched us)
        //   - warehouseActive is already 0 → CanShow no longer force-shows
        //   - g_closeTimestamp is set → re-open cooldown blocks any
        //     accidental re-trigger from a controller path that races
        //   - g_originalWndProc bypasses our own hook so we don't recurse
        if (forceClose && g_originalWndProc && g_gameWindow) {
            __try {
                CallWindowProcA(g_originalWndProc, g_gameWindow,
                                WM_KEYDOWN, VK_ESCAPE, 0x00010001);
                CallWindowProcA(g_originalWndProc, g_gameWindow,
                                WM_KEYUP,   VK_ESCAPE, 0xC0010001);
            } __except(EXCEPTION_EXECUTE_HANDLER) {}
        }
    }
}

// Snapshot of all relevant state for a single log line. Useful when
// B/Circle is blocked or when a close path runs — gives a complete
// picture of what IsNewModalDialogVisible saw and what the handler
// fields look like at that exact moment.
static void LogModalState(const char* prefix) {
    if (!g_debugLog) return;
    uintptr_t handler = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);
    LONG itemDetail = InterlockedCompareExchange(&g_itemDetailActiveCount, 0, 0);
    uint8_t  af = 0;
    uint64_t pv = 0;
    if (handler) {
        __try {
            af = *(uint8_t*)(handler + g_offActiveFlag);
            pv = *(uint64_t*)(handler + g_offPanelValue);
        } __except(EXCEPTION_EXECUTE_HANDLER) {}
    }
    Log("%s state: handler=0x%llX +PV=0x%llX +0x%X=%u modal=%d itemDetail=%ld activePanel=%ld",
        prefix, (unsigned long long)handler, (unsigned long long)pv,
        g_offActiveFlag, (unsigned)af, IsNewModalDialogVisible() ? 1 : 0,
        (long)itemDetail, (long)InterlockedCompareExchange(&g_activePanel, 0, 0));
}

// ============================================================
//  WndProc + Input
// ============================================================
// g_pendingCircleClose / g_pendingBClose are defined near the file top so
// TriggerWarehouse can clear them.

static LRESULT CALLBACK HookedWndProc(HWND h, UINT m, WPARAM w, LPARAM l) {
    if (m==WM_TRIGGER_WAREHOUSE) { TriggerWarehouse((int)w); return 0; }
    if (m==WM_INIT_WAREHOUSE) {
        // Deferred warehouse panel init — posted by InputThread (separate thread)
        // once the handler has been auto-captured by HookedCanShow.
        if (!InterlockedCompareExchange(&g_warehouseActive, 0, 0)) return 0;
        uintptr_t handler = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);
        if (handler) {
            Log("  Deferred init: handler captured, initializing panel");
            InitWarehousePanel(handler, GetInitStringForActive());
        } else {
            Log("  Deferred init: WM_INIT_WAREHOUSE but handler still NULL");
        }
        return 0;
    }
    // Panel hotkeys via WM_KEYDOWN. The game's input system sometimes leaves
    // GetAsyncKeyState reporting "still down" after a tap — polling-based
    // edge detection then misses subsequent presses. WM_KEYDOWN delivers a
    // proper press event for every physical tap (and OS auto-repeat), with
    // lParam bit 30 indicating "previous state": 0 = new press, 1 = repeat.
    // We trigger only on bit 30 == 0 so a held key produces exactly one
    // toggle action.
    if (m == WM_KEYDOWN) {
        bool autoRepeat = (l & (1LL << 30)) != 0;
        if (!autoRepeat) {
            // ESC: warehouse-close (or pass-through to dismiss modal first).
            if (w == VK_ESCAPE && InterlockedCompareExchange(&g_warehouseActive, 0, 0)) {
                if (IsNewModalDialogVisible()) {
                    // Each ESC consumes one modal: pass it to the game, clear
                    // the fallback flag and mark the dialog as dismissed.
                    InterlockedExchange(&g_itemDetailActiveCount, 0);
                    InterlockedExchange(&g_modalDismissed, 1);
                    Log("ESC pressed -> modal up, passing through to game");
                    return CallWindowProcA(g_originalWndProc, h, m, w, l);
                }
                Log("ESC pressed -> closing warehouse");
                PostMessageA(h, WM_TRIGGER_WAREHOUSE, 1, 0);
                return 0;
            }
            // Per-panel hotkeys take precedence over the legacy single
            // hotkey. With the new defaults (F4=Private, F5=Gatherables,
            // F6=Dresser, F7=Refrigerator, F8=Symbol, F9=Collecting),
            // any legacy `g_hotkey` value would collide with one of these
            // panels — checking it first would shadow the per-panel
            // binding. Legacy default is now 0 (disabled).
            for (int i = 0; i < PANEL_COUNT; i++) {
                if (g_panels[i].hotkey == 0 || (DWORD)w != g_panels[i].hotkey) continue;
                bool modOk = (g_panels[i].modifier == 0) ||
                             (GetAsyncKeyState(g_panels[i].modifier) & 0x8000) != 0;
                if (!modOk) break;
                LONG warehouseActive = InterlockedCompareExchange(&g_warehouseActive, 0, 0);
                if (!warehouseActive) {
                    InterlockedExchange(&g_nextOpenPanel, i);
                    Log("HOTKEY %s (vk=0x%X) -> OPEN", g_panels[i].name, g_panels[i].hotkey);
                } else {
                    Log("HOTKEY %s (vk=0x%X) -> CLOSE", g_panels[i].name, g_panels[i].hotkey);
                }
                PostMessageA(h, WM_TRIGGER_WAREHOUSE, 1, 0);
                return 0;
            }
            // Legacy single hotkey — only fires if no per-panel hotkey
            // matched above. Kept for backwards compatibility with INIs
            // that still use `Hotkey=` instead of the per-panel keys.
            if (g_hotkey && (DWORD)w == g_hotkey) {
                bool modOk = (g_modifierKey == 0) ||
                             (GetAsyncKeyState(g_modifierKey) & 0x8000) != 0;
                if (modOk) {
                    PostMessageA(h, WM_TRIGGER_WAREHOUSE, 1, 0);
                    return 0;
                }
            }
        }
    }
    // --- Raw Input: DualSense / DualShock buttons ---
    if (m == WM_INPUT) {
        ParseSonyButtons(l);

        bool circleDown = g_lastCircle;

        // Per-panel PSButton rising edges → toggle that panel.
        // If a PSModifier is configured, it must also be held at the moment
        // the button is pressed (mirrors XInput ControllerModifier).
        for (int i = 0; i < PANEL_COUNT; i++) {
            if (g_panels[i].psButtonByteOff < 0) {
                g_panelPsLastDown[i] = false;
                continue;
            }
            bool down = g_panelPsCurrentDown[i];
            bool modOk = (g_panels[i].psModifierByteOff < 0) ||
                         g_panelPsModifierDown[i];
            if (down && !g_panelPsLastDown[i] && modOk) {
                if (InterlockedCompareExchange(&g_warehouseActive, 0, 0)) {
                    if (IsNewModalDialogVisible()) {
                        // A dialog is up: the panel button closes neither the
                        // dialog nor the chest. Only clear the fallback flag.
                        InterlockedExchange(&g_itemDetailActiveCount, 0);
                    } else {
                        // Force close: bypass TriggerWarehouse modal-block.
                        PostMessageA(h, WM_TRIGGER_WAREHOUSE, 2, 0);
                    }
                } else {
                    InterlockedExchange(&g_nextOpenPanel, i);
                    PostMessageA(h, WM_TRIGGER_WAREHOUSE, 0, 0);
                }
            }
            g_panelPsLastDown[i] = down;
        }

        // Circle pressed while warehouse open → mark pending close (don't close yet)
        if (circleDown && !g_circleWasDown && InterlockedCompareExchange(&g_warehouseActive, 0, 0)) {
            if (IsNewModalDialogVisible()) {
                // The game sees this Circle too (WM_INPUT is passed on) and
                // dismisses the dialog with it: mirror ESC.
                InterlockedExchange(&g_itemDetailActiveCount, 0);
                InterlockedExchange(&g_modalDismissed, 1);
            } else {
                InterlockedExchange(&g_pendingCircleClose, 1);
            }
        }

        // Circle released after pending close → close (force, bypass modal-block).
        if (!circleDown && g_circleWasDown && InterlockedCompareExchange(&g_pendingCircleClose, 0, 0)) {
            InterlockedExchange(&g_pendingCircleClose, 0);
            PostMessageA(h, WM_TRIGGER_WAREHOUSE, 2, 0);
        }

        g_circleWasDown = circleDown;
    }
    return CallWindowProcA(g_originalWndProc, h, m, w, l);
}

static DWORD g_lastAct=0;
static DWORD WINAPI InputThread(LPVOID) {
    while (true) {
        Sleep(16);
        if (InterlockedCompareExchange(&g_shutdown, 0, 0)) return 0;
        if (!g_enabled||!g_ready||!g_gameWindow) continue;

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

        // InvDumpKey: log the live inventory groups (read-only debug aid).
        static bool dumpKeyDown = false;
        if (g_invDumpKey) {
            bool d = (GetAsyncKeyState(g_invDumpKey) & 0x8000) != 0;
            if (d && !dumpKeyDown) {
                dumpKeyDown = true;
                DWORD now = GetTickCount();
                if (now - g_lastAct >= 400) {
                    g_lastAct = now;
                    DumpInvGroups();
                }
            } else if (!d) dumpKeyDown = false;
        }

        // Lazy-resolve mainChar from singleton if not yet captured
        if (!InterlockedCompareExchange64(&g_mainChar, 0, 0)) {
            uintptr_t resolved = ResolveMainChar();
            if (resolved > 0x10000000000ULL) {
                InterlockedExchange64(&g_mainChar, (LONG64)resolved);
                Log("mainChar: 0x%llX (singleton, deferred)", (unsigned long long)resolved);
            }
        }

        // Deferred warehouse init: handler wasn't available when F6 was pressed.
        // We poll from this thread (16ms interval) because PostMessage from WndProc
        // re-queues before the game renders a frame.  InputThread is a separate thread
        // so the game processes frames between our checks. Timeout is generous
        // (~30 s) because newer game builds lazy-instantiate the warehouse
        // controller — Handler may not fire until many frames after F-press.
        // CaptureOnHandler ALSO triggers init inline when it captures, so this
        // poll is mostly a safety net for builds where Handler fires soon
        // enough that the WM_INIT_WAREHOUSE path is faster.
        if (InterlockedCompareExchange(&g_initPending, 0, 0)) {
            uintptr_t handler = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);
            if (handler) {
                InterlockedExchange(&g_initPending, 0);
                PostMessageA(g_gameWindow, WM_INIT_WAREHOUSE, 0, 0);
            } else {
                LONG retries = InterlockedIncrement(&g_initRetryCount);
                if (retries >= 1800) {  // ~30 seconds at 16ms
                    InterlockedExchange(&g_initPending, 0);
                    Log("  Deferred init: GAVE UP after %ld retries (~30 s) — no Handler call observed", retries);
                }
            }
        }

        // Keyboard hotkeys are dispatched from HookedWndProc
        // via WM_KEYDOWN — see panel-hotkey block there. Polling here was
        // unreliable: the game's input system left GetAsyncKeyState reporting
        // "still down" after a tap, so subsequent presses missed the rising
        // edge. WM_KEYDOWN's lParam bit 30 (previous-key-state) gives a clean
        // press-vs-repeat signal independent of hardware-state polling.

        // Controller: XInput logic mirrors the DirectInput WM_INPUT path
        // structurally — same per-panel rising-edge detection with
        // per-panel last-down trackers, same modifier check at press time,
        // same direct-PostMessage pattern, same B/Circle press-pending →
        // release-close sequence.
        if (g_pXInputGetState) {
            // Aggregate buttons across ALL XInput slots (0–3). Steam Input
            // remaps PS5 controllers to one slot, while a physical Xbox
            // controller takes another — polling only slot 0 made the mod
            // miss B presses on whichever device wasn't index 0. OR-merging
            // means any controller's B/L3/R3 press is seen.
            WORD buttons = 0;
            int liveSlots = 0;
            ULONGLONG nowHb = GetTickCount64();
            for (DWORD idx = 0; idx < 4; idx++) {
                XINPUT_STATE_LOCAL state;
                memset(&state, 0, sizeof(state));
                if (g_pXInputGetState(idx, &state) == 0) {
                    buttons |= state.Gamepad.wButtons;
                    liveSlots++;
                }
            }

            if (liveSlots > 0) {
                bool warehouseActiveBtn =
                    InterlockedCompareExchange(&g_warehouseActive, 0, 0) != 0;

                // Per-panel hold-to-close timers — each panel tracks how long
                // its open combo has been continuously held. If the user keeps
                // holding the combo AFTER the panel has opened, treat that as
                // a "hold to close" gesture. Helps users who don't realise the
                // combo needs to be re-pressed for toggle-close.
                static ULONGLONG s_panelHoldStart[PANEL_COUNT] = {0};
                static bool      s_panelHoldFiredClose[PANEL_COUNT] = {false};

                for (int i = 0; i < PANEL_COUNT; i++) {
                    WORD btn = g_panels[i].controllerButton;
                    if (!btn) {
                        g_panelXiLastDown[i] = false;
                        s_panelHoldStart[i] = 0;
                        s_panelHoldFiredClose[i] = false;
                        continue;
                    }
                    bool down = (buttons & btn) != 0;
                    WORD mod = g_panels[i].controllerModifier;
                    bool modOk = (mod == 0) || ((buttons & mod) != 0);
                    bool comboHeld = down && modOk;

                    // Rising-edge toggle
                    if (down && !g_panelXiLastDown[i] && modOk) {
                        if (warehouseActiveBtn) {
                            // Modal-aware close: with a quantity dialog or Details popup
                            // up, the panel combo (masked from the game) must not
                            // force-close the warehouse. Only clear the fallback flag;
                            // the user dismisses the dialog with B first.
                            if (IsNewModalDialogVisible()) {
                                InterlockedExchange(&g_itemDetailActiveCount, 0);
                                s_panelHoldFiredClose[i] = true;  // absorb hold-detection
                            } else {
                                InterlockedExchange(&g_itemDetailActiveCount, 0);
                                PostMessageA(g_gameWindow, WM_TRIGGER_WAREHOUSE, 2, 0);
                                s_panelHoldFiredClose[i] = true;
                            }
                        } else {
                            InterlockedExchange(&g_nextOpenPanel, i);
                            PostMessageA(g_gameWindow, WM_TRIGGER_WAREHOUSE, 0, 0);
                            s_panelHoldFiredClose[i] = false;
                        }
                        s_panelHoldStart[i] = nowHb;
                    }

                    // Hold-to-close after >700 ms continuous hold
                    if (comboHeld && warehouseActiveBtn &&
                        s_panelHoldStart[i] != 0 &&
                        !s_panelHoldFiredClose[i] &&
                        (nowHb - s_panelHoldStart[i]) >= 700) {
                        // Same modal guard as the rising-edge close path.
                        if (!IsNewModalDialogVisible()) {
                            InterlockedExchange(&g_itemDetailActiveCount, 0);
                            PostMessageA(g_gameWindow, WM_TRIGGER_WAREHOUSE, 2, 0);
                        } else {
                            InterlockedExchange(&g_itemDetailActiveCount, 0);
                        }
                        s_panelHoldFiredClose[i] = true;
                    }

                    if (!comboHeld) {
                        s_panelHoldStart[i] = 0;
                        s_panelHoldFiredClose[i] = false;
                    }

                    g_panelXiLastDown[i] = down;
                }

                // ---- B button (default close): mirrors DirectInput Circle.
                //  - Rising edge with a modal up (IsNewModalDialogVisible):
                //    the game sees this B (the IAT filter lets B through
                //    while a dialog is up) and dismisses the dialog with it;
                //    mark the dialog dismissed, like ESC. Do NOT mark pending
                //    close so the release doesn't close the warehouse too.
                //  - Rising edge with no modal: mark pending. Falling edge
                //    triggers warehouse-close (force, bypass modal-block).
                bool bDown = (buttons & 0x2000) != 0;
                if (bDown && !g_xiBWasDown && warehouseActiveBtn) {
                    if (IsNewModalDialogVisible()) {
                        InterlockedExchange(&g_itemDetailActiveCount, 0);
                        InterlockedExchange(&g_modalDismissed, 1);
                    } else {
                        InterlockedExchange(&g_pendingBClose, 1);
                    }
                }
                if (!bDown && g_xiBWasDown && InterlockedCompareExchange(&g_pendingBClose, 0, 0)) {
                    InterlockedExchange(&g_pendingBClose, 0);
                    PostMessageA(g_gameWindow, WM_TRIGGER_WAREHOUSE, 2, 0);
                }
                g_xiBWasDown = bDown;

                g_prevButtons = buttons;
            }
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

    // Step 2: SetInventory = the CALL after the "SetInventory" strcmp in the
    // Handler. The neighbouring SetChannels helper is rejected by size: it is a
    // small function with a RET in its first 0x40 bytes, SetInventory is not.
    if (g_fnHandler) {
        uintptr_t strSetInv = FindString("SetInventory");
        if (strSetInv) {
            uintptr_t leaAddr = FindLEA(strSetInv, g_fnHandler);
            if (leaAddr && leaAddr < g_fnHandler + 0x1000) {
                uintptr_t targets[16];
                int n = FindAllCALLsAfter(leaAddr, 60, targets, 16);
                for (int i = 0; i < n; i++) {
                    uint8_t* p = (uint8_t*)targets[i];
                    // Accept the usual large-function prologs:
                    //   40 55            (REX PUSH RBP)
                    //   48 89 4C 24 08   (MOV [RSP+8], RCX)
                    //   48 89 5C 24 ??   (MOV [RSP+disp8], RBX)
                    bool prologOk = false;
                    if (p[0] == 0x40 && p[1] == 0x55) prologOk = true;
                    else if (p[0] == 0x48 && p[1] == 0x89 && p[2] == 0x4C && p[3] == 0x24 && p[4] == 0x08) prologOk = true;
                    else if (p[0] == 0x48 && p[1] == 0x89 && p[2] == 0x5C && p[3] == 0x24) prologOk = true;
                    if (!prologOk) continue;
                    // Size guard: SetChannels has a RET within its first 0x40
                    // bytes, SetInventory does not.
                    bool earlyRet = false;
                    for (int k = 1; k < 0x40; k++) {
                        if (p[k] == 0xC3) { earlyRet = true; break; }
                    }
                    if (earlyRet) continue;
                    g_fnSetInventory = targets[i];
                    break;
                }
            }
        }
    }
    Log("SetInventory: %s base+0x%llX (string-xref)", g_fnSetInventory?"OK":"FAIL",
        g_fnSetInventory?(unsigned long long)(g_fnSetInventory-g_gameBase):0);

    if (!g_fnSetInventory) {
        Log("SetInventory: WARN dynamic resolver failed — panel binding will not work this session");
    }

    // Step 3: Find SetTitle via "SetWareHouseInventoryName" string → CALL chain in Handler
    if (g_fnHandler) {
        uintptr_t strSetName = FindString("SetWareHouseInventoryName");
        if (strSetName) {
            uintptr_t leaAddr = FindLEA(strSetName, g_fnHandler);
            if (leaAddr && leaAddr < g_fnHandler + 0x1000) {
                // The branch loads the title node, then hands it to the setter:
                //     MOV r64, [handlerReg+disp32]    ; node (this is BottomLabel's load)
                //     ...
                //     MOV RCX, r64                    ; same register
                //     CALL setter                     ; E8 rel32
                // Register- and offset-flexible so it survives struct re-layouts.
                for (int i = 0; i < 0x140 && !g_fnSetTitle; i++) {
                    uint8_t* p = (uint8_t*)(leaAddr + i);
                    if (p[0] < 0x48 || p[0] > 0x4F || p[1] != 0x8B) continue;
                    if ((p[2] & 0xC0) != 0x80 || (p[2] & 0x07) == 0x04) continue;
                    uint32_t disp = *(uint32_t*)(p + 3);
                    if (disp < 0x100 || disp >= 0x1000) continue;
                    int nodeReg = (((p[0] >> 2) & 1) << 3) | ((p[2] >> 3) & 7);  // REX.R : ModRM.reg
                    for (int j = i + 7; j < i + 0x60; j++) {
                        uint8_t* q = (uint8_t*)(leaAddr + j);
                        if (q[0] != 0x48 && q[0] != 0x49) continue;
                        if (q[1] != 0x8B) continue;
                        if ((q[2] & 0xF8) != 0xC8) continue;           // mod=11, reg=RCX
                        int srcReg = ((q[0] & 1) << 3) | (q[2] & 7);   // REX.B : ModRM.rm
                        if (srcReg != nodeReg) continue;
                        if (q[3] != 0xE8) continue;
                        int32_t rel = *(int32_t*)(q + 4);
                        uintptr_t target = (uintptr_t)(q + 8) + rel;
                        if (target > g_gameBase && target < g_gameBase + g_imageSize)
                            g_fnSetTitle = target;
                        break;
                    }
                }
            }
        }
    }
    Log("SetTitle:     %s base+0x%llX (string-xref)", g_fnSetTitle?"OK":"FAIL",
        g_fnSetTitle?(unsigned long long)(g_fnSetTitle-g_gameBase):0);

    // Step 3a: Extract bottom-label offset from the handler's SetWareHouseInventoryName branch.
    // The handler does:  uVar3 = *(undefined8 *)(param_1 + OFFSET);  ...  SetTitle(uVar3, text);
    // The LOAD ("mov r64, [rXX+disp32]", opcode 48 8B, ModRM mod=10) sits within ~0x100 bytes
    // before the CALL to SetTitle.  Take the MATCH NEAREST to the CALL.
    if (g_fnHandler && g_fnSetTitle) {
        uintptr_t strSetName = FindString("SetWareHouseInventoryName");
        if (strSetName) {
            uintptr_t leaAddr = FindLEA(strSetName, g_fnHandler);
            if (leaAddr && leaAddr < g_fnHandler + 0x1000) {
                // Locate the CALL to g_fnSetTitle after leaAddr
                uintptr_t callSite = 0;
                for (int i = 0; i < 400; i++) {
                    uint8_t* p = (uint8_t*)(leaAddr + i);
                    if (p[0] != 0xE8) continue;
                    int32_t rel = *(int32_t*)(p + 1);
                    if ((uintptr_t)(p + 5) + rel == g_fnSetTitle) {
                        callSite = leaAddr + i;
                        break;
                    }
                }
                if (callSite) {
                    // Walk backwards from callSite looking for MOV r64, [rXX+disp32]
                    // Encoding: REX.W (48-4F), 8B, ModRM (mod=10 → 0x80-0xBF), optional SIB, disp32
                    uint32_t bestDisp = 0;
                    for (uintptr_t a = callSite - 3; a > leaAddr; a--) {
                        uint8_t* p = (uint8_t*)a;
                        if (p[0] < 0x48 || p[0] > 0x4F) continue;
                        if (p[1] != 0x8B) continue;
                        if ((p[2] & 0xC0) != 0x80) continue;      // mod must be 10
                        int dispOff = 3;
                        if ((p[2] & 0x07) == 0x04) dispOff = 4;    // SIB byte present
                        uint32_t disp = *(uint32_t*)(p + dispOff);
                        if (disp >= 0x100 && disp < 0x1000) {
                            bestDisp = disp;
                            break;  // closest match wins
                        }
                    }
                    if (bestDisp) g_offBottomLabel = bestDisp;
                }
            }
        }
    }
    Log("BottomLabel:  %s offset=0x%X (handler → SetTitle callsite)",
        g_offBottomLabel ? "OK" : "FAIL", g_offBottomLabel);

    // Step 3b: TopTitle offset via the UI selector-attribute binding chain.
    // The top header title is the NpcInteractionTitle widget's text node
    // (#NpcInteractionTitleText); the warehouse body attribute
    // "selector-title-subtext-stage" is bound to a member of the control.
    // Mechanism cross-check: resolving "selector-warehouse-inventory-title"
    // the same way must reproduce the BottomLabel offset that Step 3a
    // extracted from the SetWareHouseInventoryName branch. If anything
    // disagrees, DISABLE the top-title write instead of falling back to the
    // compiled-in default, which may point at a different bound node.
    {
        uint32_t prevDefault = g_offTopTitle;
        uint32_t offTop   = ResolveSelectorMemberOffset("selector-title-subtext-stage");
        uint32_t offCheck = ResolveSelectorMemberOffset("selector-warehouse-inventory-title");
        if (offTop && offCheck && g_offBottomLabel && offCheck == g_offBottomLabel) {
            g_offTopTitle = offTop;
            Log("TopTitle:     OK offset=0x%X (selector binding chain; cross-check inv-title=0x%X == BottomLabel; default was 0x%X)",
                g_offTopTitle, offCheck, prevDefault);
        } else {
            g_offTopTitle = 0;
            Log("TopTitle:     DISABLED (binding chain top=0x%X check=0x%X bottomLabel=0x%X) — top title stays generic",
                offTop, offCheck, g_offBottomLabel);
        }
    }

    // Step 3c: Find SetDonationFaction handler via "SetDonationFaction" string-xref in
    // the main warehouse handler, and extract the donation-state struct offset.
    // The donation handler writes 3 shorts (faction type) and on the failure path
    // resets them to 0xFFFF via `MOV word [RDI+disp32], BX` where BX = 0xFFFF.
    // Encoding: 66 89 9F disp32 (ModRM 0x9F = mod=10, reg=011 (BX), r/m=111 (RDI)).
    // Generalize to any base register: 66 89 9X disp32 with mod=10, reg=011.
    //
    // The handler dispatches commands via `strcmp(...); JNZ skip; setup; CALL handler`.
    // strcmp always comes first after the LEA. We filter it out by call-target proximity
    // (library functions sit far from the Handler in the binary); the target handler is
    // always co-located within ~1 MB of the dispatcher Handler.
    if (g_fnHandler) {
        uintptr_t strDonation = FindString("SetDonationFaction");
        if (strDonation) {
            uintptr_t leaAddr = FindLEA(strDonation, g_fnHandler);
            if (leaAddr && leaAddr < g_fnHandler + 0x1000) {
                uintptr_t targets[16];
                int n = FindAllCALLsAfter(leaAddr, 200, targets, 16);
                for (int i = 0; i < n; i++) {
                    uintptr_t t = targets[i];
                    if (t == g_fnSetInventory || t == g_fnSetTitle) continue;
                    uintptr_t dist = (t > g_fnHandler) ? (t - g_fnHandler) : (g_fnHandler - t);
                    if (dist > 0x100000) continue;   // skip strcmp/library calls (far from Handler)
                    g_fnSetDonationFaction = t;
                    break;
                }
            }
        }
    }
    Log("SetDonationFaction: %s base+0x%llX",
        g_fnSetDonationFaction ? "OK" : "FAIL",
        g_fnSetDonationFaction ? (unsigned long long)(g_fnSetDonationFaction - g_gameBase) : 0);
    // Scan SetDonationFaction for `66 89 9X disp32` (MOV word [reg+disp32], BX)
    // Take the smallest disp32 found — that's the first of the 3 donation-state shorts.
    if (g_fnSetDonationFaction) {
        uint8_t* fn = (uint8_t*)g_fnSetDonationFaction;
        uint32_t smallest = 0;
        for (int j = 0; j < 0x400 - 7; j++) {
            // Must be: 0x66 (operand size prefix), 0x89 (MOV r/m16, r16), ModRM with
            // mod=10 and reg=011 (BX).  That's ModRM byte = 0x98 | r/m in [0..7] minus r/m=100 (SIB).
            if (fn[j] != 0x66 || fn[j+1] != 0x89) continue;
            uint8_t modrm = fn[j+2];
            if ((modrm & 0xC0) != 0x80) continue;     // mod=10
            if ((modrm & 0x38) != 0x18) continue;     // reg=011 (BX)
            if ((modrm & 0x07) == 0x04) continue;     // r/m != SIB
            uint32_t disp = *(uint32_t*)(fn + j + 3);
            if (disp < 0x100 || disp >= 0x1000) continue;
            if (!smallest || disp < smallest) smallest = disp;
        }
        if (smallest) g_offDonationState = smallest;
    }
    Log("DonationOff:  %s offset=0x%X (SetDonationFaction → MOV [reg+N],BX)",
        g_fnSetDonationFaction ? "OK" : "FALLBACK", g_offDonationState);

    // Step 3d: Extract 0x15 "prepare" sub-object offsets directly from the Handler body.
    // The Handler's 0x15 path does three back-to-back virtual calls of the form:
    //     MOV RCX, [param_1+disp32]   ; REX 8B ModRM(mod=10, reg=001 RCX, r/m != SIB) disp32
    //     MOV RAX, [RCX]              ; 48 8B 01
    //     CALL [RAX+imm]              ; FF 50 disp8  OR  FF 90 disp32
    if (g_fnHandler) {
        uint8_t* fn = (uint8_t*)g_fnHandler;
        uint32_t offs[3] = {};
        int found = 0;
        for (int i = 0; i < 0x200 && found < 3; i++) {
            if (fn[i] < 0x40 || fn[i] > 0x4F) continue;        // REX prefix
            if (fn[i + 1] != 0x8B) continue;                    // MOV r64, r/m64
            uint8_t modrm = fn[i + 2];
            if ((modrm & 0xC0) != 0x80) continue;               // mod = 10 (disp32)
            if ((modrm & 0x38) != 0x08) continue;               // reg = 001 (RCX target)
            if ((modrm & 0x07) == 0x04) continue;               // skip SIB-encoded r/m
            uint32_t disp = *(uint32_t*)(fn + i + 3);
            if (disp < 0x100 || disp > 0x800) continue;         // plausible struct offset
            int movRaxPos = i + 7;
            if (fn[movRaxPos] != 0x48 || fn[movRaxPos + 1] != 0x8B || fn[movRaxPos + 2] != 0x01) continue;
            int callPos = movRaxPos + 3;
            if (fn[callPos] != 0xFF) continue;
            if (fn[callPos + 1] != 0x50 && fn[callPos + 1] != 0x90) continue;
            bool dup = false;
            for (int j = 0; j < found; j++) if (offs[j] == disp) { dup = true; break; }
            if (dup) continue;
            offs[found++] = disp;
        }
        if (found == 3) {
            g_offPrepare1 = offs[0];
            g_offPrepare2 = offs[1];
            g_offPrepare3 = offs[2];
        }
        Log("PrepareOffs:  %s offs=0x%X/0x%X/0x%X (handler scan)",
            found == 3 ? "OK" : "FALLBACK",
            g_offPrepare1, g_offPrepare2, g_offPrepare3);
    }

    // Step 4: Find CanShow via Handler's vtable (update-proof — scans all vtable entries)
    // CanShow signature: MOVZX EAX, byte [this+disp32] followed by RET (reads the
    // active flag; 0x118 on 1.0x, 0x130 since 2.01.00).
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
                // Check CanShow signature.  CanShow's hot path ends with:
                //     movzx eax, byte ptr [thisPtr+disp32]
                //     ret                              (optionally preceded by stack cleanup)
                // We require: MOVZX destination is EAX (reg field = 000), mod = 10 (disp32),
                // r/m != 100 (no SIB), and the instruction is followed within a few bytes by
                // a RET (C3).  Constraining reg=000 rules out the many unrelated MOVZX uses
                // that would otherwise produce false positives on arbitrary virtual functions.
                uint8_t* fn = (uint8_t*)resolved;
                uint32_t matchDisp = 0;
                for (int j = 0; j < 0x200 - 8 && !matchDisp; j++) {
                    uint8_t* p = fn + j;
                    int instrLen = 0;
                    uint32_t d = 0;
                    // Case A: 0F B6 8X disp32  (MOVZX eax/ecx/edx... from [reg+disp32])
                    // We want reg=000 (EAX), so modrm in 0x80-0x87 (but not 0x84 = SIB)
                    if (p[0] == 0x0F && p[1] == 0xB6 &&
                        (p[2] & 0xF8) == 0x80 && p[2] != 0x84) {
                        d = *(uint32_t*)(p + 3);
                        instrLen = 7;
                    }
                    // Case B: REX prefix + MOVZX (8 bytes total)
                    // REX byte 0x44 adds R bit to target reg — for EAX target no REX.R needed.
                    // REX 0x48 is W (64-bit), but MOVZX doesn't use W.  Only REX.B (0x41) would
                    // change the source base register.  Accept REX bytes 0x40-0x47 (no R bit).
                    else if (p[0] >= 0x40 && p[0] <= 0x47 &&
                             p[1] == 0x0F && p[2] == 0xB6 &&
                             (p[3] & 0xF8) == 0x80 && p[3] != 0x84) {
                        d = *(uint32_t*)(p + 4);
                        instrLen = 8;
                    }
                    if (!instrLen || d < 0x40 || d >= 0x2000) continue;
                    // Require a RET within 6 bytes after the MOVZX (allows short epilog like
                    // `add rsp, XX; ret` or `pop rbp; ret`).
                    bool retNearby = false;
                    for (int k = 0; k < 6; k++) {
                        if (p[instrLen + k] == 0xC3) { retNearby = true; break; }
                    }
                    if (!retNearby) continue;
                    matchDisp = d;
                }
                if (matchDisp) {
                    g_fnCanShow = resolved;
                    g_warehouseVtableEntry = vtableEntry;
                    g_offActiveFlag = matchDisp;
                    Log("  Vtable at base+0x%llX, CanShow at base+0x%llX (vtable offset 0x%llX), active flag offset 0x%X",
                        (unsigned long long)(vtableEntry - g_gameBase),
                        (unsigned long long)(resolved - g_gameBase),
                        (unsigned long long)(v - vtableEntry), matchDisp);
                }
            }
        }
    }
    Log("CanShow:      %s base+0x%llX (vtable)", g_fnCanShow?"OK":"FAIL",
        g_fnCanShow?(unsigned long long)(g_fnCanShow-g_gameBase):0);

    // PanelValue sits in the same struct as the active flag and moves with it.
    // The flag is derived from CanShow's body, so it gives the struct delta for
    // free: 0x110 was correct while the flag sat at 0x118; on 2.01.00 the flag
    // is 0x130, i.e. PanelValue is 0x128.
    if (g_offActiveFlag) {
        const uint32_t kFlagRef = 0x118;   // build where the 0x110 default held
        int32_t delta = (int32_t)g_offActiveFlag - (int32_t)kFlagRef;
        if (delta != 0) {
            int32_t shifted = (int32_t)g_offPanelValue + delta;
            if (shifted > 0x10 && shifted < 0x2000) {
                Log("PanelValue:   0x%X -> 0x%X (panel struct moved %+d, from active flag 0x%X)",
                    g_offPanelValue, shifted, delta, g_offActiveFlag);
                g_offPanelValue = (uint32_t)shifted;
            } else {
                Log("PanelValue:   struct delta %+d would give an implausible 0x%X — keeping 0x%X",
                    delta, shifted, g_offPanelValue);
            }
        } else {
            Log("PanelValue:   0x%X (active flag at the reference offset, no shift)",
                g_offPanelValue);
        }
    }

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

    // Step 5a: game-manager singleton (mainChar = *(*(global) + 0x48)). The
    // load pair
    //     MOV rX, [rip+global]     ; manager singleton slot
    //     MOV rY, [rX + 0x48]      ; mainChar
    // is ambiguous on its own, so accept it only when ONE global clearly
    // dominates — the game manager is referenced far more often than any other
    // object with a +0x48 member. Build 25116796: 14 candidates, winner 247
    // sites vs 22 for the runner-up. ResolveMainChar reads through it under SEH
    // and nothing is ever written through it.
    {
        if (!g_mainCharGlobalPtr) {
            struct Cand { uintptr_t g; int n; };
            Cand cand[64] = {};
            int nc = 0, overflow = 0;
            uint8_t* base = (uint8_t*)g_gameBase;
            for (DWORD i = 0; (size_t)i + 11 < g_imageSize; i++) {
                if (base[i] != 0x48 && base[i] != 0x4C) continue;
                if (base[i+1] != 0x8B || (base[i+2] & 0xC7) != 0x05) continue;
                int dst = (((base[i] >> 2) & 1) << 3) | ((base[i+2] >> 3) & 7);
                uint8_t* q = base + i + 7;
                if (q[0] != 0x48 && q[0] != 0x49 && q[0] != 0x4C && q[0] != 0x4D) continue;
                if (q[1] != 0x8B) continue;
                uint8_t m = q[2];
                if ((m & 0xC0) != 0x40 || (m & 0x07) == 0x04) continue;
                if (q[3] != 0x48) continue;                       // member +0x48
                int src = ((q[0] & 1) << 3) | (m & 0x07);
                if (src != dst) continue;                         // same register
                int32_t disp = *(int32_t*)(base + i + 3);
                uintptr_t g = (uintptr_t)(base + i + 7) + disp;
                if (g <= g_gameBase || g >= g_gameBase + g_imageSize) continue;
                int k = 0;
                for (; k < nc; k++) if (cand[k].g == g) { cand[k].n++; break; }
                if (k == nc) {
                    if (nc < 64) { cand[nc].g = g; cand[nc].n = 1; nc++; }
                    else overflow++;
                }
            }
            uintptr_t best = 0;
            int bestN = 0, secondN = 0;
            for (int k = 0; k < nc; k++) {
                if (cand[k].n > bestN) { secondN = bestN; bestN = cand[k].n; best = cand[k].g; }
                else if (cand[k].n > secondN) secondN = cand[k].n;
            }
            if (best && bestN >= 20 && bestN >= secondN * 4) {
                g_mainCharGlobalPtr = best;
                Log("MainCharGlobal: OK base+0x%llX (dominant +0x48 global: %d sites vs %d runner-up, %d candidates)",
                    (unsigned long long)(g_mainCharGlobalPtr - g_gameBase), bestN, secondN, nc);
            } else {
                Log("MainCharGlobal: fallback inconclusive (best=%d runner-up=%d candidates=%d overflow=%d)",
                    bestN, secondN, nc, overflow);
            }
        }
        if (!g_mainCharGlobalPtr) Log("MainCharGlobal: FAIL (singleton pattern not found)");
    }

    // Step 5b: ModeSwitcher (the view-tag configurator) via the unique
    // "ingame-global" string xref. Only its location is needed: the screen id
    // that mounts the warehouse view is read out of its jump tables below.
    {
        uintptr_t strIG = FindString("ingame-global");
        uintptr_t leaAddr = strIG ? FindLEA(strIG) : 0;
        g_fnModeSwitcher = leaAddr ? FindFunctionStart(leaAddr) : 0;
        Log("ModeSwitcher: %s base+0x%llX (string-xref)", g_fnModeSwitcher ? "OK" : "FAIL",
            g_fnModeSwitcher ? (unsigned long long)(g_fnModeSwitcher - g_gameBase) : 0ULL);
    }

    // Step 5c: the game's own menu request queue and the screen id whose
    // ModeSwitcher case emits the "store" view tag (WareHouseView is declared
    // tag2="store ingamemenu" in uigameconfig2.xml).
    ResolvePanelLookup();

    if (ResolveMenuRequest()) {
        g_storeScreenId = ResolveStoreScreenId();
        if (g_storeScreenIdIni >= 0)
            Log("StoreScreenId: INI override %d in use (derived was %d)",
                g_storeScreenIdIni, g_storeScreenId);
        if (EffectiveStoreScreenId() < 0)
            Log("StoreScreenId: unresolved — set StoreScreenId in the INI");
    }

    // Step 7: Find language byte dynamically
    // The Steam API init function compares Steam's language string
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

    // InventoryInfo manager (RTTI, see ResolveInventoryMgrViaRtti); the records
    // are patched by the worker thread once the instance exists.
    ResolveInventoryMgrViaRtti();

    // Session global for the live inventory container (see ActorViaSessionGlobal):
    // the global that is by far most often loaded and then dereferenced at +0x30.
    // Build 25116796: base+0x6C29760 with 1353 sites vs 500 for the runner-up.
    // ResolveInvContainer() validates whatever this yields before using it.
    {
        struct Cand { uintptr_t g; int n; };
        Cand cand[64] = {};
        int nc = 0;
        uint8_t* base = (uint8_t*)g_gameBase;
        for (DWORD i = 0; (size_t)i + 11 < g_imageSize; i++) {
            if (base[i] != 0x48 && base[i] != 0x4C) continue;
            if (base[i+1] != 0x8B || (base[i+2] & 0xC7) != 0x05) continue;
            int dst = (((base[i] >> 2) & 1) << 3) | ((base[i+2] >> 3) & 7);
            uint8_t* q = base + i + 7;
            if (q[0] != 0x48 && q[0] != 0x49 && q[0] != 0x4C && q[0] != 0x4D) continue;
            if (q[1] != 0x8B) continue;
            uint8_t m = q[2];
            if ((m & 0xC0) != 0x40 || (m & 0x07) == 0x04) continue;
            if (q[3] != 0x30) continue;                       // member +0x30
            int src = ((q[0] & 1) << 3) | (m & 0x07);
            if (src != dst) continue;                         // same register
            int32_t disp = *(int32_t*)(base + i + 3);
            uintptr_t g = (uintptr_t)(base + i + 7) + disp;
            if (g <= g_gameBase || g >= g_gameBase + g_imageSize) continue;
            int k = 0;
            for (; k < nc; k++) if (cand[k].g == g) { cand[k].n++; break; }
            if (k == nc && nc < 64) { cand[nc].g = g; cand[nc].n = 1; nc++; }
        }
        uintptr_t best = 0; int bestN = 0, secondN = 0;
        for (int k = 0; k < nc; k++) {
            if (cand[k].n > bestN) { secondN = bestN; bestN = cand[k].n; best = cand[k].g; }
            else if (cand[k].n > secondN) secondN = cand[k].n;
        }
        if (best && bestN >= 20 && bestN >= secondN * 2) {
            g_sessionGlobal = best;
            Log("SessionGlobal: OK base+0x%llX (dominant +0x30 global: %d sites vs %d runner-up, %d candidates)",
                (unsigned long long)(best - g_gameBase), bestN, secondN, nc);
        } else {
            Log("SessionGlobal: inconclusive (best=%d runner-up=%d) — cluster scan fallback only",
                bestN, secondN);
        }
    }

    // ItemDetailModal open handler — resolved via the "ItemDetailModalMessage"
    // string LEA xref (walk back from the LEA to the function prolog).
    g_addrItemDetailCtor = 0;
    {
        uintptr_t strModal = FindString("ItemDetailModalMessage");
        if (strModal) {
            uintptr_t leaAddr = FindLEA(strModal);
            if (leaAddr) {
                uintptr_t fnStart = FindFunctionStart(leaAddr);
                if (fnStart) {
                    g_addrItemDetailCtor = fnStart;
                    Log("ItemDetailCtor:      OK base+0x%llX (string-xref \"ItemDetailModalMessage\")",
                        (unsigned long long)(fnStart - g_gameBase));
                }
            }
        }
        if (!g_addrItemDetailCtor) {
            Log("ItemDetailCtor:      WARN string-xref failed — \"View Details\" popup detection disabled (ESC may close warehouse instead of popup)");
        }
    }
    // Quantity dialog opener, same way ("CountingModalMessage" string LEA xref).
    g_addrCountingModal = 0;
    {
        uintptr_t strCnt = FindString("CountingModalMessage");
        uintptr_t leaAddr = strCnt ? FindLEA(strCnt) : 0;
        uintptr_t fnStart = leaAddr ? FindFunctionStart(leaAddr) : 0;
        if (fnStart) {
            g_addrCountingModal = fnStart;
            Log("CountingModal:       OK base+0x%llX (string-xref \"CountingModalMessage\")",
                (unsigned long long)(fnStart - g_gameBase));
        } else {
            Log("CountingModal:       WARN string-xref failed — a quantity dialog re-opened while the modal layer fades is not detected");
        }
    }

    return g_fnHandler && g_fnCanShow && g_fnSetInventory && g_mainCharGlobalPtr &&
           g_menuRequestFn && EffectiveStoreScreenId() >= 0;
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

    Log("=== Private Storage Anywhere v1.6.0 (CD 2.02.00) ===");
    {char cls[256]={};char ttl[256]={};GetClassNameA(g_gameWindow,cls,256);GetWindowTextA(g_gameWindow,ttl,256);
    Log("Game window: class='%s' title='%s'",cls,ttl);}
    g_gameBase=(uintptr_t)GetModuleHandleA("CrimsonDesert.exe");
    if(!g_gameBase){Log("FATAL: no game base");return 0;}
    MODULEINFO mi;GetModuleInformation(GetCurrentProcess(),(HMODULE)g_gameBase,&mi,sizeof(mi));
    g_imageSize=mi.SizeOfImage;
    Log("Base: 0x%llX  Size: 0x%X  LegacyHotkey: 0x%02X",
        (unsigned long long)g_gameBase, g_imageSize, g_hotkey);
    for (int i = 0; i < PANEL_COUNT; i++) {
        Log("  Panel[%d] %-12s: kb=0x%02X mod=0x%02X xi=0x%04X xiMod=0x%04X "
            "psBtn=(off=%d,mask=0x%02X) psMod=(off=%d,mask=0x%02X)",
            i, g_panels[i].name,
            g_panels[i].hotkey, g_panels[i].modifier,
            g_panels[i].controllerButton, g_panels[i].controllerModifier,
            g_panels[i].psButtonByteOff, g_panels[i].psButtonBitMask,
            g_panels[i].psModifierByteOff, g_panels[i].psModifierBitMask);
    }

    // Hash meta/0.papgt to detect modded game files (JSON mods etc.)
    // Find game root by locating \bin64\ in the DLL path (works regardless of subdirectory depth)
    {
        std::string metaPath(dp);
        size_t bin64pos = metaPath.rfind("\\bin64\\");
        if (bin64pos == std::string::npos)
            bin64pos = metaPath.rfind("\\bin64");  // DLL directly in bin64 (no trailing subdir)
        if (bin64pos != std::string::npos)
            metaPath = metaPath.substr(0, bin64pos);
        else {
            // Fallback: strip filename + one dir (legacy layout)
            size_t bs = metaPath.rfind('\\');
            if (bs != std::string::npos) metaPath = metaPath.substr(0, bs);
            bs = metaPath.rfind('\\');
            if (bs != std::string::npos) metaPath = metaPath.substr(0, bs);
        }
        metaPath += "\\meta\\0.papgt";
        uint32_t crc = FileCRC32(metaPath.c_str());
        if (crc) Log("meta/0.papgt CRC32: %08X", crc);
        else     Log("meta/0.papgt: NOT FOUND");
    }

    if(!ResolveAddresses()){Log("FATAL: pattern scan failed");return 0;}

    // Compute hook size: find clean instruction boundary >= 14 bytes; fall
    // back to fixed 15 if the decoder bails on an unknown opcode. Local —
    // original bytes for cleanup are recorded by InstallHook into g_hookTable.
    int hookSizeHandler = FindPrologBoundary((uint8_t*)g_fnHandler, 14);
    if (hookSizeHandler < 14) hookSizeHandler = 15;

    if(!InstallHook(g_fnHandler,(uintptr_t)&CaptureOnHandler,"Handler",hookSizeHandler)) return 0;
    if(!InstallCanShowHook(g_fnCanShow)) return 0;

    // Read-only hook that seeds the panel manager for the game-menu gate.
    // Non-fatal: without it the gate simply stays off.
    if (g_fnFindPanelTop) {
        if (!InstallHook(g_fnFindPanelTop, (uintptr_t)&CaptureOnFindPanelTop, "FindPanelTop"))
            Log("FindPanelTop hook FAILED — game-menu gate disabled");
    }

    // ItemDetailOpen hook: raises g_itemDetailActiveCount so ESC/B/Circle close
    // the popup first instead of the warehouse.
    if (g_addrItemDetailCtor) {
        if (!InstallHook(g_addrItemDetailCtor, (uintptr_t)&CaptureOnItemDetailCtor,
                         "ItemDetailOpen")) {
            Log("ItemDetailOpen hook FAILED — popup won't be detected");
        }
    }
    if (g_addrCountingModal) {
        if (!InstallHook(g_addrCountingModal, (uintptr_t)&CaptureOnCountingModal,
                         "CountingModalOpen")) {
            Log("CountingModalOpen hook FAILED");
        }
    }

    // Resolve mainChar immediately from singleton (no need to wait for hook callback)
    {
        uintptr_t mc = ResolveMainChar();
        if (mc > 0x10000000000ULL) {
            InterlockedExchange64(&g_mainChar, (LONG64)mc);
            Log("mainChar: 0x%llX (singleton)", (unsigned long long)mc);
        } else {
            Log("mainChar: DEFERRED (singleton not ready yet)");
        }
    }

    InitXInput();

    // IAT-hook the game's XInputGetState so its own polling never sees
    // mod-bound combos or B-while-warehouse-open. Mod's own poll uses
    // g_pXInputGetState (direct DLL export) which bypasses the IAT.
    InstallXInputIATHook((HMODULE)g_gameBase);

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
    RegisterRawInputDevices(rid, 2, sizeof(RAWINPUTDEVICE));

    g_ready=true;
    CreateThread(nullptr,0,InputThread,nullptr,0,nullptr);

    // Slot-capacity worker: raise the five housing records to their maximum as
    // soon as the InventoryInfo manager instance exists, then exit. The records
    // are not re-created during a session, and every open re-checks them
    // synchronously (InitWarehousePanel), so no periodic background writes
    // are needed.
    if (g_invMgrGlobal) {
        CreateThread(nullptr, 0, [](LPVOID) -> DWORD {
            for (int tick = 0; tick < 1800; tick++) {          // give up after ~30 min
                if (InterlockedCompareExchange(&g_shutdown, 0, 0)) return 0;
                int n = PatchSlotsViaManager();
                if (n > 0) {
                    Log("Slot capacity: %d housing chest(s) at maximum — worker done", n);
                    return 0;
                }
                Sleep(1000);
            }
            Log("Slot capacity: worker gave up — inventory records never appeared");
            return 0;
        }, nullptr, 0, nullptr);
    } else {
        Log("Slot capacity: InventoryInfo manager unresolved — housing chests keep their vanilla capacity");
    }

    Log("=== READY ===");
    return 0;
}

BOOL APIENTRY DllMain(HMODULE h,DWORD r,LPVOID){
    if(r==DLL_PROCESS_ATTACH){g_hModule=h;DisableThreadLibraryCalls(h);CreateThread(nullptr,0,ModThread,nullptr,0,nullptr);}
    else if(r==DLL_PROCESS_DETACH){
        // Signal worker threads to exit BEFORE we touch shared resources.
        // We cannot WaitForSingleObject here (loader-lock deadlock risk),
        // so this is best-effort: workers next wakeup will see the flag.
        InterlockedExchange(&g_shutdown, 1);
        if(g_gameWindow&&g_originalWndProc)SetWindowLongPtrA(g_gameWindow,GWLP_WNDPROC,(LONG_PTR)g_originalWndProc);
        RemoveXInputIATHook();
        // Restore original bytes for every installed hook so a DLL unload
        // (hot-reload of the ASI) leaves the game in a clean state. The
        // table is populated by InstallHook + InstallCanShowHook.
        DWORD op;
        for (int i = 0; i < g_hookCount; i++) {
            HookEntry& e = g_hookTable[i];
            if (!e.addr || e.size <= 0) continue;
            VirtualProtect((void*)e.addr, e.size, PAGE_EXECUTE_READWRITE, &op);
            memcpy((void*)e.addr, e.orig, e.size);
            VirtualProtect((void*)e.addr, e.size, op, &op);
            FlushInstructionCache(GetCurrentProcess(), (void*)e.addr, e.size);
        }
        if(g_hXInput){FreeLibrary(g_hXInput);g_hXInput=nullptr;}
        if(g_logFile){
            FILE* lf = g_logFile;
            g_logFile = nullptr;  // gate Log() before fclose so racing worker writes are no-ops
            fprintf(lf, "=== Unloaded (hooks restored) ===\n");
            fclose(lf);
        }
    }
    return TRUE;
}
