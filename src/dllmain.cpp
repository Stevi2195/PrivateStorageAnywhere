#include <windows.h>
#include <psapi.h>
#include <intrin.h>
#include <cstdio>
#include <cstring>
#include <string>

// ============================================================
//  Private Storage Anywhere v1.4.1
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
static uintptr_t g_fnHideSubCtrl = 0;  // FUN_140b99b40: hides a UI sub-controller (symmetric to FUN_140b999c0 show)
static uintptr_t g_warehouseVtableEntry = 0;  // vtable address containing handler — used for auto-capture verification
static uintptr_t g_warehouseVtableStart = 0;  // vtable start of warehouse class — set on first successful capture
static uint32_t  g_modalDialogOff = 0;     // handler+N: move-quantity dialog pointer
static uintptr_t g_langByteAddr = 0;      // address of language byte (resolved dynamically from Steam API init function)

// Struct offsets — all resolved dynamically from game code at runtime (update-proof).
// Defaults match the build in which each offset was first discovered; they serve as
// a sane fallback if the dynamic resolver fails.  DO NOT use the default values
// directly in code — always go through these variables.
static uint32_t g_offActiveFlag   = 0x118;  // handler+N: u8 active flag (read by CanShow)
static uint32_t g_offPanelValue   = 0x110;  // handler+N: panel value (set by base-class 0x0e)
static uint32_t g_offBottomLabel  = 0x308;  // handler+N: cpp-ware-house-inventory-title node
static uint32_t g_offTopTitle     = 0x0E0;  // handler+N: top title / NpcInteractionTitle node
static uint32_t g_offSubObject    = 0x08;   // handler+N: ptr to sub-object (contains panelId)
static uint32_t g_offSubPanelId   = 0x92;   // subObject+N: u16 panelId
static uint32_t g_offModeByte     = 0xCA8;  // mainChar+N: u8 current mode
static uint32_t g_offSubByte      = 0xCA9;  // mainChar+N: u8 current sub-mode
static uint32_t g_offModeFlags    = 0xCB1;  // mainChar+N: mode flag array (7 bytes)
static uint32_t g_offSubtypes     = 0xCB8;  // mainChar+N: subtype array (16 bytes)
static uint32_t g_offDonationState = 0x330; // handler+N: first of 3 donation faction shorts (cleared on open)
static uintptr_t g_fnSetDonationFaction = 0; // handler for "SetDonationFaction" command — scanned for donation-state offset
// 0x15 "prepare" sub-object offsets — game's 0x15 dispatcher does 3 virtual calls on these.
// Must be validated non-null before sending an empty 0x15, otherwise the dispatcher crashes
// (sub-objects are only initialized after NPC interaction).  Resolved dynamically from the
// Handler body (scan for 3 consecutive `MOV RCX,[param_1+disp32]; MOV RAX,[RCX]; CALL [RAX+imm]`).
// Defaults match the pre-Apr-11 game layout; the Apr-23 layout is 0x2e8/0x2f8/0x320.
static uint32_t g_offPrepare1 = 0x2c8;
static uint32_t g_offPrepare2 = 0x2d8;
static uint32_t g_offPrepare3 = 0x300;
static uintptr_t g_mainCharGlobalPtr = 0;   // address of global singleton pointer; mainChar = *(*(globalPtr) + 0x48)

// Captured game state (accessed from multiple threads via Interlocked ops)
static volatile LONG64 g_mainChar = 0;
// Single handler slot. The Gatherables Chest uses the SAME UIGamePlayControlRootWarehouse2
// controller (same panelId 0x0058, same vtable) as Private Storage — they differ only in
// which SetInventory filter string is passed when opening. So we track one handler and
// switch inventories by re-calling SetInventory with the other string.
static volatile LONG64 g_handlerThis = 0;
static volatile LONG64 g_cursorObj = 0;
static volatile LONG g_warehouseActive = 0;
static volatile LONG g_handlerHitCount = 0;
static volatile LONG g_canShowSeen118 = 0;  // set to 1 once +0x118 has been seen as 1

// Active panel selector. F6 opens PRIVATE; F7/F8/F9/F12/Num0 open the housing
// chests directly. Each press is a fresh open from cold.
enum ActivePanel {
    PANEL_PRIVATE      = 0,  // CampWareHouse (Private Storage, ~640 slots)
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
    const char* name;              // English logging name
    char        initString[256];   // SetInventory filter (overridable via INI)
    DWORD       hotkey;            // Keyboard VK code, 0 = no dedicated hotkey
    DWORD       modifier;          // Keyboard VK code, 0 = no modifier
    WORD        controllerButton;  // XInput button mask, 0 = no button
    WORD        controllerModifier; // XInput hold-this-first mask, 0 = no modifier
    int         psButtonByteOff;   // PS5/PS4 HID: byte offset from buttons1; -1 = unbound
    BYTE        psButtonBitMask;   // PS5/PS4 HID: bit mask within that byte
};
static PanelDef g_panels[PANEL_COUNT] = {
    { "Private",      "Character,Focus,True;CampWareHouse,Focus,True",                0,            0, 0, 0, -1, 0 },
    { "Gatherables",  "Character,Focus,True;Housing_GatheredMaterials,Focus,True",   0x76 /*F7*/,  0, 0, 0, -1, 0 },
    { "Dresser",      "Character,Focus,True;Housing_Dresser,Focus,True",              0x77 /*F8*/,  0, 0, 0, -1, 0 },
    { "Refrigerator", "Character,Focus,True;Housing_Refrigerator,Focus,True",         0x78 /*F9*/,  0, 0, 0, -1, 0 },
    { "Symbol",       "Character,Focus,True;Housing_Symbol,Focus,True",               0,            0, 0, 0, -1, 0 },
    { "Collecting",   "Character,Focus,True;Housing_Collecting,Focus,True",           0x60 /*Num0*/,0, 0, 0, -1, 0 },
};
// Per-panel last-down state for PS button edge detection (parallel to g_panels[]).
static bool g_panelPsLastDown[PANEL_COUNT] = {};
static bool g_panelPsCurrentDown[PANEL_COUNT] = {};

// Constants
static volatile LONG g_warehousePanelId = 0x0059;  // default, verified dynamically at runtime

// Per-panel panelValue (handler+0x110). The game sets this from a type-0x05 sub-command
// in the 0x0e-show packet (parsed as uint64 from string via strtoull). Our 0x0e packet
// has no sub-commands, so panelValue stays at 0 and the container isn't bound.
// Workaround: after the 0x0e call, write panelValue manually for the active panel.
// For Gatherables we look up the per-session ID via the global Inventory-Type
// hash-map at runtime (see LookupInventoryTypeId).
static volatile LONG g_privatePanelValueCfg     = 0;       // 0 = no override
static volatile LONG g_gatherablesPanelValueCfg = 0;       // 0 = use runtime lookup

// Resolved addresses (Weg F).
// DAT_145e8f768 holds a POINTER to the canonical "Housing_GatheredMaterials" string.
// FUN_14ee1ecd0 takes a string pointer and writes a 16-bit panel-ID into out param 2.
// Internally it walks a global lookup table populated at game-init.
static uintptr_t g_pHGMStringSlot = 0;       // Address of the slot holding the string pointer
static uintptr_t g_fnTypeNameLookup = 0;     // Address of the lookup function

// Cached panel-id resolved via hash-map lookup once per session.
static volatile LONG g_resolvedGatherablesId = 0;  // 0 = not resolved yet, -1 = lookup failed

// === Container singleton-factory diagnostics (Weg G — under investigation) ===
// Goal: locate the in-game singleton that owns the GC container vtable so we can
// call its CreateContainer method without an NPC visit. RE findings (1.0.4.2):
//
//   Container vtable                  : base+0x4A7D610 (the bound object at handler+0x170)
//   Container alloc size              : 0x8f8 bytes
//   Factory wrapper (alloc+construct) : base+0xA9EDC10
//   Constructor                       : base+0xC910D0
//
//   Singleton-with-CreateContainer    : vtable base+0x4A5BE00
//   Vtable[1] = JMP-thunk -> factory  : base+0xC235D0 (calls factory, single arg = self)
//   Singleton-getter (lazy create)    : base+0xA7CDFB0
//   Type-ID slot for singleton        : base+0x5E3D654 (uint32, hash-map key)
// RVAs verified for 1.0.4.2 (type-ID at base+0x5E3D654 reads 0x09EA, matching
// the value found in the post-NPC-visit container's +0x18 field). The full
// factory call works at runtime — see TryCreateContainerViaSingleton below.
static uintptr_t g_addrContainerVtable      = 0;  // base+0x4A7D610
static uintptr_t g_addrFactorySingletonVt   = 0;  // base+0x4A5BE00
static uintptr_t g_addrSingletonTypeIdSlot  = 0;  // base+0x5E3D654
static uintptr_t g_addrSingletonGetter      = 0;  // base+0xA7CDFB0
static uintptr_t g_addrFactoryWrapper       = 0;  // base+0xA9EDC10

// InventoryInfoManager singleton ptr-of-ptr. Layout (verified via Ghidra
// FUN_1404e9780 — GetInventoryInfo by InventoryKey):
//   *(mgr + 0x08) = uint32 count
//   *(mgr + 0x50) = InventoryInfo*[] (8 bytes per entry, indexed by key)
// InventoryInfo + 0x48 = ushort base slot count (default 10 for housing,
// 640 for CampWareHouse). FUN_1404de7c0 reads it as the "max slots" base
// before adding character expansions. Patching this at runtime updates
// every consumer (UI, item put-in, etc).
static uintptr_t g_addrInventoryInfoMgrPtr  = 0;  // base+0x5F0DA18 (= &DAT_145f0da18)
static volatile LONG g_inventorySlotPatchApplied = 0;

// Captured factory call state. When the game calls FUN_14a9edc10 (e.g. while
// the player approaches the housing chest and the chest object loads), our
// hook records the singleton (RCX) and controller (RDX) it was called with.
// These are real, fully-initialized game objects — much more useful than the
// fake-owner / heap-scanned controller we synthesize ourselves.
static volatile LONG64 g_capturedFactorySingleton = 0;
static volatile LONG64 g_capturedFactoryCtrl      = 0;
static volatile LONG   g_capturedFactoryHits      = 0;

// Per-panel sticky-binding state. When a warehouse panel is active and the
// game has written a valid container pointer into handler+0x170, we save it
// indexed by the currently-active panel. On a later open/switch to that
// panel we restore the saved pointer (after validating its vtable). Without
// per-panel storage, all housing panels would share Gatherables's container
// and show the wrong items.
static volatile LONG64 g_panelStickyContainer[PANEL_COUNT] = {};
// Tracks which panel's container is currently bound to handler+0x170. When
// we switch to a different panel, we force a re-bind so SetInventory sees
// the correct inventory pool.
static volatile LONG g_currentBoundPanel = -1;

// In-place handler/sub-field patching: when F7 opens GC, we don't replace the
// container at handler+0x170 (that crashes — and pre-NPC it's NULL anyway).
// Instead we patch a few specific fields on the warehouse handler that
// control panel-mode and capacity. Values from post-NPC memory diff +
// runtime field-scan (handler+0x39C identified as the max-slots field).
static volatile LONG64 g_patchedContainer  = 0;   // handler we patched (0 = none)
static volatile LONG   g_savedCamp_9C      = 0;
static volatile LONG   g_savedCamp_A0      = 0;
static volatile LONG   g_savedCamp_84      = 0;
static volatile LONG   g_savedCamp_B8      = 0;
static volatile LONG   g_savedCamp_39C     = 0;   // handler+0x39C = max-slots
static volatile LONG   g_campValuesSaved   = 0;

// Diff-Snapshot scaffolding: handler-object + sub-object + container-object
// (handler+0x170 → container). The container holds max-slots/capacity etc.
#define HANDLER_SNAPSHOT_SIZE  0x800
#define SUB_SNAPSHOT_SIZE      0x800
#define CONT_SNAPSHOT_SIZE     0x800
static uint8_t g_snapshotBefore[HANDLER_SNAPSHOT_SIZE]    = {};
static uint8_t g_snapshotAfter[HANDLER_SNAPSHOT_SIZE]     = {};
static uint8_t g_subSnapshotBefore[SUB_SNAPSHOT_SIZE]     = {};
static uint8_t g_subSnapshotAfter[SUB_SNAPSHOT_SIZE]      = {};
static uint8_t g_contSnapshotBefore[CONT_SNAPSHOT_SIZE]   = {};
static uint8_t g_contSnapshotAfter[CONT_SNAPSHOT_SIZE]    = {};
static volatile LONG64 g_subSnapshotAddr                  = 0;
static volatile LONG64 g_contBeforeAddr                   = 0;
static volatile LONG64 g_contAfterAddr                    = 0;
static volatile LONG g_snapshotState = 0;
static DWORD g_diffSnapshotKey = 0x79;  // VK_F10
static DWORD g_diffSnapshotModifier = 0;

// Set by the hotkey handler right before posting WM_TRIGGER_WAREHOUSE. The Open path
// in TriggerWarehouse reads this and sets g_activePanel accordingly, then resets it.
static volatile LONG g_nextOpenPanel = PANEL_PRIVATE;

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
static uint16_t GetGatherablesPanelId(void);
static uint16_t LookupInventoryTypeId(uintptr_t pTypeHash);
static uint16_t GetPanelTypeId(int panelIdx);
static uintptr_t ResolveContainerForPanelId(uintptr_t handler, uint16_t panelId);
static uintptr_t TryCreateContainerViaSingleton(uintptr_t handler);
static void InitWarehousePanel(uintptr_t handler, const char* initString);

// GetInitStringForActive: returns the SetInventory filter string for the currently active panel.
static inline const char* GetInitStringForActive() {
    LONG i = InterlockedCompareExchange(&g_activePanel, 0, 0);
    if (i < 0 || i >= PANEL_COUNT) i = PANEL_PRIVATE;
    return g_panels[i].initString;
}

// Hook cleanup: saved original bytes for safe DLL unload
static uint8_t g_origHandlerBytes[20] = {};
static uint8_t g_origModeSwitcherBytes[20] = {};
static uint8_t g_origCanShowBytes[14] = {};
static int g_hookSizeHandler = 15, g_hookSizeModeSwitcher = 15;
static uintptr_t g_hookAddrHandler = 0, g_hookAddrModeSwitcher = 0, g_hookAddrCanShow = 0;



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
    Log("HID device identified: VID=%04X PID=%04X → buttons1 offset=%d",
        SONY_VID, pid, g_cachedReportOffset);
}

// Parses Circle + per-panel PSButton state from WM_INPUT HID report.
// Stores results in g_lastCircle and g_panelPsCurrentDown[].
static void ParseSonyButtons(LPARAM lParam) {
    g_lastCircle = false;
    for (int i = 0; i < PANEL_COUNT; i++) g_panelPsCurrentDown[i] = false;

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

    // Per-panel PSButton state. Each panel that has a binding gets its
    // current pressed state populated; panels without binding stay false.
    for (int i = 0; i < PANEL_COUNT; i++) {
        if (g_panels[i].psButtonByteOff < 0) {
            g_panelPsCurrentDown[i] = false;
            continue;
        }
        int psOff = offset + g_panels[i].psButtonByteOff;
        if ((DWORD)psOff < reportLen) {
            g_panelPsCurrentDown[i] = (report[psOff] & g_panels[i].psButtonBitMask) != 0;
        } else {
            g_panelPsCurrentDown[i] = false;
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

// English-only titles for the additional housing panels. Localization can be
// added later by following the per-language pattern used in GetPrivateStorageTitle.
static const char* GetDresserTitle()      { return "Dresser"; }
static const char* GetRefrigeratorTitle() { return "Refrigerator"; }
static const char* GetSymbolTitle()       { return "Symbol Storage"; }
static const char* GetCollectingTitle()   { return "Collecting Storage"; }

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
            // childCount == 0: no modal visible.
            // childCount > 0x100: freed-memory garbage (modal was dismissed, pointer not cleared
            // — reading at the old address returns whatever the allocator wrote). Treat as dismissed.
            if (childCount == 0 || childCount > 0x100) {
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
    g_hotkey = ReadHexValue("Settings", "Hotkey", VK_F6, p);
    g_modifierKey = ReadHexValue("Settings", "ModifierKey", 0, p);
    g_controllerButton = (WORD)ReadHexValue("Settings", "ControllerButton", 0, p);
    g_controllerModifier = (WORD)ReadHexValue("Settings", "ControllerModifier", 0, p);
    g_reloadKey = ReadHexValue("Settings", "ReloadKey", 0, p);

    g_diffSnapshotKey      = ReadHexValue("Settings", "DiffSnapshotKey",      0x79, p);
    g_diffSnapshotModifier = ReadHexValue("Settings", "DiffSnapshotModifier", 0,    p);

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

    // PSButton (legacy global) → seeds Private's panel slot. Existing user
    // INIs with PSButton=Share keep working.
    char psBtn[32];
    GetPrivateProfileStringA("Settings", "PSButton", "none", psBtn, sizeof(psBtn), p);
    int legacyOff; BYTE legacyMask;
    if (ParsePSButtonName(psBtn, &legacyOff, &legacyMask)) {
        g_panels[PANEL_PRIVATE].psButtonByteOff = legacyOff;
        g_panels[PANEL_PRIVATE].psButtonBitMask = legacyMask;
        Log("Legacy PSButton=%s → Private (byteOff=%d bitMask=0x%02X)", psBtn, legacyOff, legacyMask);
    }

    // Per-panel <Name>PSButton overrides. Reads same name strings (Share,
    // Circle, Cross, ...).
    for (int i = 0; i < PANEL_COUNT; i++) {
        char keyName[64];
        snprintf(keyName, sizeof(keyName), "%sPSButton", kIniKey[i]);
        char buf[32] = {};
        GetPrivateProfileStringA("Settings", keyName, "", buf, sizeof(buf), p);
        if (!buf[0]) continue;  // not set in INI → keep current binding
        int off; BYTE mask;
        if (ParsePSButtonName(buf, &off, &mask)) {
            g_panels[i].psButtonByteOff = off;
            g_panels[i].psButtonBitMask = mask;
            Log("Panel %s PSButton=%s (byteOff=%d bitMask=0x%02X)",
                g_panels[i].name, buf, off, mask);
        } else {
            g_panels[i].psButtonByteOff = -1;
            g_panels[i].psButtonBitMask = 0;
        }
    }
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
        __try {
            uintptr_t sub = *(uintptr_t*)((uint8_t*)thisPtr + g_offSubObject);
            if (sub) {
                uint16_t realId = *(uint16_t*)((uint8_t*)sub + g_offSubPanelId);
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

// Walk the InventoryInfoManager singleton and patch every InventoryInfo's
// base slot count (ushort at +0x48) from 10 to 1000. Found via Ghidra:
// FUN_1404e9780 (GetInventoryInfo by InventoryKey) reads from
// *(manager + 0x50)[key], FUN_1404de7c0 reads (info + 0x48) as the slot base.
// Returns number of entries patched, or -1 if manager not yet loaded.
static int PatchInventoryInfoSlots() {
    if (!g_addrInventoryInfoMgrPtr) return -1;
    int patched = 0;
    __try {
        uintptr_t mgr = *(uintptr_t*)g_addrInventoryInfoMgrPtr;
        if (!mgr) return -1;
        uint32_t count = *(uint32_t*)(mgr + 8);
        uintptr_t arr  = *(uintptr_t*)(mgr + 0x50);
        if (!arr || count == 0 || count > 4096) return -1;
        for (uint32_t i = 0; i < count; i++) {
            uintptr_t info = *(uintptr_t*)(arr + i * 8);
            if (!info) continue;
            uint16_t* pSlots = (uint16_t*)(info + 0x48);
            if (*pSlots == 10) {
                *pSlots = 1000;
                patched++;
            }
        }
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        Log("PatchInventoryInfoSlots: SEH exception");
        return -1;
    }
    return patched;
}

// Hook on the container factory FUN_14a9edc10. Fires whenever the game (any
// code path — chest load, NPC interaction, panel re-init, etc.) builds a new
// 0x8f8 housing-storage container. We snapshot the args (singleton + ctrl)
// because they're the FULLY-INITIALIZED versions of objects that are normally
// hidden inside the housing system. With these in hand, our F7 path can call
// the factory itself with real game data instead of synthesized stubs.
extern "C" void __fastcall CaptureOnFactory(void* owner, void* ctrl) {
    InterlockedIncrement(&g_capturedFactoryHits);
    LONG hits = InterlockedCompareExchange(&g_capturedFactoryHits, 0, 0);
    InterlockedExchange64(&g_capturedFactorySingleton, (LONG64)(uintptr_t)owner);
    InterlockedExchange64(&g_capturedFactoryCtrl,      (LONG64)(uintptr_t)ctrl);
    // Log only the very first hit — diagnostic, confirms hook installed.
    if (hits == 1) {
        Log("Factory hook installed (first call: singleton=0x%llX ctrl=0x%llX)",
            (unsigned long long)(uintptr_t)owner,
            (unsigned long long)(uintptr_t)ctrl);
    }
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

extern "C" void __fastcall CaptureModeSwitcher(void* rcx) {
    if (!g_mainChar) {
        uintptr_t mc = ResolveMainChar();
        if (mc > 0x10000000000ULL) {
            InterlockedExchange64(&g_mainChar, (LONG64)mc);
            Log("CAPTURED mainChar: 0x%llX (via singleton)", (unsigned long long)mc);

            // Capture cursorObj via pointer chain: mainChar+0x50 -> +0x60 -> deref -> +0x78
            __try {
                uintptr_t container = *(uintptr_t*)((uint8_t*)mc + 0x50);
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
            memcpy(mc + g_offModeFlags, g_savedModes, 7);
            memcpy(mc + g_offSubtypes, g_savedSubtypes, 15);
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

    // Auto-capture warehouse controller by exact vtable match. All 6 panels
    // share this controller — the per-panel inventory binding happens via
    // SetInventory with the panel's filter string during InitWarehousePanel.
    if (g_warehouseVtableStart && (uintptr_t)thisPtr != handler) {
        __try {
            uintptr_t objVtable = *(uintptr_t*)thisPtr;
            if (objVtable == g_warehouseVtableStart) {
                uintptr_t sub = *(uintptr_t*)((uint8_t*)thisPtr + g_offSubObject);
                uint16_t panelId = sub ? *(uint16_t*)((uint8_t*)sub + g_offSubPanelId) : 0xFFFF;
                InterlockedExchange64(&g_handlerThis, (LONG64)(uintptr_t)thisPtr);
                handler = (uintptr_t)thisPtr;
                if (panelId != 0xFFFF && panelId != 0)
                    InterlockedExchange(&g_warehousePanelId, (LONG)panelId);
                Log("AUTO-CAPTURED warehouse controller: 0x%llX (panelId=0x%04X)",
                    (unsigned long long)thisPtr, panelId);

                // Fix for first-open-empty: when we just captured the handler
                // AND a F6/F7 trigger is currently waiting on init, run
                // InitWarehousePanel inline on the game thread NOW. This is
                // the same thread that's about to render the panel, so when
                // CanShow returns the panel renders WITH our SetInventory +
                // PanelValue + Title already applied. The WM_INIT_WAREHOUSE
                // posted by InputThread later still runs but is a no-op
                // because g_initPending was cleared.
                if (InterlockedCompareExchange(&g_initPending, 0, 0)) {
                    InterlockedExchange(&g_initPending, 0);
                    Log("  CanShow: running InitWarehousePanel inline (first-open fix)");
                    InitWarehousePanel(handler, GetInitStringForActive());
                }
            }
        } __except(EXCEPTION_EXECUTE_HANDLER) {}
    }

    if (InterlockedCompareExchange(&g_warehouseActive, 0, 0)) {
        if (handler && (uintptr_t)thisPtr == handler) {
            __try {
                uint8_t activeFlag = *(uint8_t*)((uint8_t*)thisPtr + g_offActiveFlag);
                if (activeFlag == 1) {
                    // Panel is alive — remember we've seen it active
                    InterlockedExchange(&g_canShowSeen118, 1);
                } else if (activeFlag == 0 && InterlockedCompareExchange(&g_canShowSeen118, 0, 0)) {
                    // active flag went from 1→0: game closed the panel (B/Circle/Cancel3)
                    Log("  CanShow: game-initiated close detected (active flag 1→0)");
                    InterlockedExchange(&g_warehouseActive, 0);
                    InterlockedExchange(&g_canShowSeen118, 0);
                    InterlockedExchange(&g_modeSwitchByMod, 0);
                    uintptr_t mc = (uintptr_t)InterlockedCompareExchange64(&g_mainChar, 0, 0);
                    if (mc) {
                        while (InterlockedCompareExchange(&g_modeByteLock, 1, 0) != 0) { _mm_pause(); }
                        memcpy((uint8_t*)mc + g_offModeFlags, g_savedModes, 7);
                        memcpy((uint8_t*)mc + g_offSubtypes, g_savedSubtypes, 15);
                        InterlockedExchange(&g_modeByteLock, 0);
                    }
                    return g_origCanShow(thisPtr);
                }
            } __except(EXCEPTION_EXECUTE_HANDLER) {}
            return 1;   // WareHouseView: force show
        }
        // Blanket suppress ALL other panels while warehouse is active.
        // Do NOT delegate to origCanShow here — it has internal side-effects
        // that corrupt game state and cause the warehouse to reappear during
        // subsequent NPC interactions.
        __try {
            uintptr_t sub = *(uintptr_t*)((uint8_t*)thisPtr + g_offSubObject);
            uint16_t pid = sub ? *(uint16_t*)((uint8_t*)sub + g_offSubPanelId) : 0xFFFF;
            uint8_t flag = *(uint8_t*)((uint8_t*)thisPtr + g_offActiveFlag);
            if (flag)
                Log("  CanShow: suppressed panel 0x%04X (active=%d, thisPtr=0x%llX)",
                    pid, flag, (unsigned long long)thisPtr);
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
// NOTE: FF 25 (JMP [rip+disp32]) thunks are excluded — they work correctly in
// trampolines because the inline 8-byte target address is copied alongside.
static bool ContainsRipRelative(uint8_t* code, int len) {
    for (int i = 0; i < len - 2; i++) {
        uint8_t b = code[i];
        // Non-REX: CALL [rip+disp32] = FF 15 xx xx xx xx (ModRM 0x15: mod=00, r/m=101)
        // (FF 25 is JMP thunk — safe to relocate because inline data follows, so skip it)
        if (b == 0xFF && i + 5 < len && code[i + 1] == 0x15) return true;
        // Non-REX MOV/LEA etc. with RIP-relative: opcode + ModRM(mod=00, r/m=101)
        if ((b == 0x8B || b == 0x8D || b == 0x89 || b == 0x3B || b == 0x39 || b == 0x63) &&
            i + 5 < len && (code[i + 1] & 0xC7) == 0x05) return true;
        // REX-prefixed (0x40-0x4F): same checks on the byte after REX
        if (b >= 0x40 && b <= 0x4F && i + 2 < len) {
            uint8_t op = code[i + 1];
            if (op == 0x8D || op == 0x8B || op == 0x89 || op == 0x3B || op == 0x39 ||
                op == 0x63 || op == 0x0F) {
                uint8_t modrm = code[i + 2];
                if ((modrm & 0xC7) == 0x05)
                    return true;
            }
            // REX + FF 15 (CALL [rip+disp32])
            if (op == 0xFF && i + 6 < len && code[i + 2] == 0x15) return true;
        }
    }
    return false;
}

// Find the smallest instruction boundary >= minBytes in a typical MSVC x86-64 prologue.
// Handles common prologue patterns: MOV [RSP+N], REG; PUSH; SUB RSP; LEA RBP; MOV RBP,RSP
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
        // REX.W prefix (48/4C): decode next opcode for length
        if (b == 0x48 || b == 0x4C) {
            uint8_t op = code[pos+1];
            // MOV r/m, reg or MOV reg, r/m with ModRM
            if (op == 0x89 || op == 0x8B) {
                uint8_t modrm = code[pos+2];
                uint8_t mod = modrm >> 6, rm = modrm & 0x07;
                if (mod == 0x01) { pos += 4 + (rm == 0x04 ? 1 : 0); continue; } // [reg+disp8] (+SIB)
                if (mod == 0x03) { pos += 3; continue; } // reg,reg (e.g. MOV RBP,RSP = 48 8B EC)
            }
            // SUB RSP, imm8: 48 83 EC xx
            if (op == 0x83 && code[pos+2] == 0xEC) { pos += 4; continue; }
            // SUB RSP, imm32: 48 81 EC xx xx xx xx
            if (op == 0x81 && code[pos+2] == 0xEC) { pos += 7; continue; }
            // LEA RBP, [RSP+disp8]: 48 8D 6C 24 xx
            if (op == 0x8D) {
                uint8_t modrm = code[pos+2];
                uint8_t mod = modrm >> 6, rm = modrm & 0x07;
                if (mod == 0x01) { pos += 4 + (rm == 0x04 ? 1 : 0); continue; }
                if (mod == 0x02) { pos += 7 + (rm == 0x04 ? 1 : 0); continue; }
            }
        }
        // JMP [RIP+disp32] thunk: FF 25 xx xx xx xx + 8-byte inline address = 14 bytes
        if (b == 0xFF && code[pos+1] == 0x25) { pos += 14; continue; }
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
    uint8_t orig[32]; memcpy(orig, (void*)func, hookSize);
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
    Log("HOOK %s: OK base+0x%llX (size=%d)",name,(unsigned long long)(func-g_gameBase),hookSize);
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
//  Warehouse panel initialization (handler-dependent steps)
//  Called from TriggerWarehouse when handler is available, or
//  deferred via WM_INIT_WAREHOUSE when handler wasn't captured yet.
// ============================================================
static void InitWarehousePanel(uintptr_t handler, const char* initString) {
    // Clear stale modal dialog pointer from previous warehouse sessions
    if (g_modalDialogOff) {
        __try {
            *(uintptr_t*)(handler + g_modalDialogOff) = 0;
            Log("  Cleared stale modal pointer at +0x%X", g_modalDialogOff);
        } __except(EXCEPTION_EXECUTE_HANDLER) {}
    }

    // Activate warehouse panel via the game's own base-class handler (command 0x0e).
    if (g_fnHandler) {
        __try {
            uint8_t showPacket[24] = {};
            showPacket[0] = 0x0e;  // base-class "show panel" command
            typedef void (__fastcall *PFN_Handler)(void*, void*);
            ((PFN_Handler)g_fnHandler)((void*)handler, (void*)showPacket);
            Log("  Panel shown via 0x0e command");
        } __except(EXCEPTION_EXECUTE_HANDLER) {
            Log("  Panel show via 0x0e EXCEPTION, falling back to manual");
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

    // Override panelValue (handler+0x110) for the active panel. The 0x0e dispatcher
    // reads this from a type-0x05 sub-command in the packet (parsed via strtoull),
    // but our packet has no sub-commands so it defaults to 0. For Housing-Chests this
    // is required so the container is bound — otherwise SetInventory loads items but
    // the container metadata (max-slots etc.) stays at the Camp default.
    //
    // For Gatherables: prefer the runtime hash-map lookup (per-session ID), fall back
    // to INI-configured static value if lookup fails.
    {
        LONG act = InterlockedCompareExchange(&g_activePanel, 0, 0);
        if (act < 0 || act >= PANEL_COUNT) act = PANEL_PRIVATE;
        LONG pv  = 0;
        const char* src = "none";
        if (act == PANEL_PRIVATE) {
            pv = InterlockedCompareExchange(&g_privatePanelValueCfg, 0, 0);
            src = "INI";
        } else {
            // Per-panel lookup: each housing namespace (Gatherables, Dresser,
            // Refrigerator, Symbol, Collecting) maps to its own 2-byte type-id
            // via the same hash-map resolver. The id binds handler+0x110 to
            // the right container metadata.
            uint16_t resolved = GetPanelTypeId(act);
            if (resolved != 0xFFFF && resolved != 0) {
                pv = (LONG)resolved;
                src = "per-panel hash-map";
            } else {
                pv = InterlockedCompareExchange(&g_gatherablesPanelValueCfg, 0, 0);
                src = "INI fallback (Gatherables)";
            }
        }
        if (pv != 0) {
            __try {
                *(uintptr_t*)(handler + 0x110) = (uintptr_t)pv;
                Log("  PanelValue override: handler+0x110 = 0x%llX (%s, source=%s)",
                    (unsigned long long)(uintptr_t)pv,
                    g_panels[act].name, src);
            } __except(EXCEPTION_EXECUTE_HANDLER) {
                Log("  PanelValue override EXCEPTION");
            }
        }

        // Container at handler+0x170 is NULL without an NPC visit (the 0x0e
        // panel-show command, which would normally bind Camp's container, throws
        // an exception in our flow). So we can't patch a container that doesn't
        // exist. Instead, patch the handler & sub fields directly — these match
        // exactly the byte changes captured in the post-NPC memory diff.
        //
        // Per-panel field state from the diff (Camp default → GC after-NPC):
        //   handler+0x1D8 (u32):   0x00000000 → 0xFFFFFFFF
        //   handler+0x200 (u8 ):   0x01 → 0x00
        //   handler+0x2A8 (u32):   0xFFFFFFFF → 0x00000000
        //   sub+0x0B5     (u8 ):   0xD0 → 0xC0
        //   sub+0x0B6     (u8 ):   0x02 → 0x00
        //   sub+0x276     (u8 ):   0x02 → 0x00
        //   sub+0x435     (u8 ):   0x14 → 0x10  ← possibly the "10" we see
        //
        // Save originals on first F7, restore on F6 to avoid Camp regression.
        {
            __try {
                uintptr_t sub = *(uintptr_t*)(handler + 0x8);
                if (act != PANEL_PRIVATE) {  // any housing panel (Gatherables/Dresser/...)
                    if (!InterlockedCompareExchange(&g_campValuesSaved, 0, 0)) {
                        InterlockedExchange(&g_savedCamp_84, (LONG)*(uint32_t*)(handler + 0x1D8));
                        InterlockedExchange(&g_savedCamp_9C, (LONG)*(uint32_t*)(handler + 0x2A8));
                        InterlockedExchange(&g_savedCamp_A0,
                            sub ? (LONG)(uint32_t)(*(uint16_t*)(sub + 0xB5) | (*(uint8_t*)(sub + 0x276) << 16) | (*(uint8_t*)(sub + 0x435) << 24)) : 0);
                        InterlockedExchange(&g_savedCamp_B8, (LONG)(*(uint8_t*)(handler + 0x200)));
                        InterlockedExchange(&g_savedCamp_39C, (LONG)*(uint32_t*)(handler + 0x39C));
                        InterlockedExchange(&g_campValuesSaved, 1);
                        Log("  Saved Camp state: handler+0x1D8=0x%X +0x200=0x%X +0x2A8=0x%X "
                            "+0x39C=%u sub+0xB5=0x%X +0xB6=0x%X +0x276=0x%X +0x435=0x%X",
                            *(uint32_t*)(handler + 0x1D8),
                            (unsigned)*(uint8_t*)(handler + 0x200),
                            *(uint32_t*)(handler + 0x2A8),
                            *(uint32_t*)(handler + 0x39C),
                            sub ? (unsigned)*(uint8_t*)(sub + 0xB5) : 0,
                            sub ? (unsigned)*(uint8_t*)(sub + 0xB6) : 0,
                            sub ? (unsigned)*(uint8_t*)(sub + 0x276) : 0,
                            sub ? (unsigned)*(uint8_t*)(sub + 0x435) : 0);
                    }
                    // Apply GC state. Conservative: only handler+0x39C (verified
                    // safe in earlier tests). The 0x388, sub+0xAA0/0xAA4 patches
                    // crashed the game — those addresses overlap real pointers
                    // or critical struct fields.
                    *(uint32_t*)(handler + 0x1D8) = 0xFFFFFFFF;
                    *(uint8_t* )(handler + 0x200) = 0x00;
                    *(uint32_t*)(handler + 0x2A8) = 0x00000000;
                    *(uint32_t*)(handler + 0x39C) = 1000;

                    // Aggressive patches removed — they crashed the game by
                    // hitting non-slot fields (pointers / state). The displayed
                    // "10" comes from a location we cannot safely reach.
                    if (sub) {
                        *(uint8_t*)(sub + 0xB5)  = 0xC0;
                        *(uint8_t*)(sub + 0xB6)  = 0x00;
                        *(uint8_t*)(sub + 0x276) = 0x00;
                        *(uint8_t*)(sub + 0x435) = 0x10;
                    }

                    InterlockedExchange64(&g_patchedContainer, (LONG64)handler);
                    Log("  Patched handler+sub for housing panel");

                } else {
                    if (InterlockedCompareExchange(&g_campValuesSaved, 0, 0)) {
                        *(uint32_t*)(handler + 0x1D8) = (uint32_t)InterlockedCompareExchange(&g_savedCamp_84, 0, 0);
                        *(uint8_t* )(handler + 0x200) = (uint8_t )InterlockedCompareExchange(&g_savedCamp_B8, 0, 0);
                        *(uint32_t*)(handler + 0x2A8) = (uint32_t)InterlockedCompareExchange(&g_savedCamp_9C, 0, 0);
                        *(uint32_t*)(handler + 0x39C) = (uint32_t)InterlockedCompareExchange(&g_savedCamp_39C, 0, 0);
                        if (sub) {
                            uint32_t packed = (uint32_t)InterlockedCompareExchange(&g_savedCamp_A0, 0, 0);
                            *(uint8_t*)(sub + 0xB5)  = (uint8_t)(packed       & 0xFF);
                            *(uint8_t*)(sub + 0xB6)  = (uint8_t)((packed >> 8 ) & 0xFF);
                            *(uint8_t*)(sub + 0x276) = (uint8_t)((packed >> 16) & 0xFF);
                            *(uint8_t*)(sub + 0x435) = (uint8_t)((packed >> 24) & 0xFF);
                        }
                        Log("  Restored Camp handler+sub state");
                    }
                }
            } __except(EXCEPTION_EXECUTE_HANDLER) {
                Log("  Handler/sub patch EXCEPTION");
            }
        }

        // Also bind the container-pointer in handler+0x170. The game does this
        // implicitly during a real chest-open at the NPC; we replicate it here
        // so F7 works without any NPC visit.
        //
        // Try in order:
        //   (1) Singleton-factory path: ask the game's own ContainerFactory
        //       singleton to construct a fresh container. Works without NPC visit
        //       once UI subsystem is initialized.
        //   (2) Static-array fallback: look up by panelId in the 133-element
        //       global container array. Only works for panels that ARE in that
        //       array (Camp Warehouse, Bank, etc — NOT Gatherables).
        // Container binding strategy (per-panel — runs for ALL panels incl. Private):
        //   1. Identify the active panel.
        //   2. If handler+0x170 holds the container for a *different* panel
        //      (g_currentBoundPanel != act), force-clear so SetInventory
        //      rebinds. Without this clear, switching panels keeps the
        //      previous container and shows its items under a new title.
        //   3. Restore from g_panelStickyContainer[active] if available
        //      and its vtable still matches.
        //   4. Otherwise leave NULL — SetInventory + the game's natural
        //      bind logic will populate it (and the sticky poller in
        //      InputThread will pick it up next tick).
        {
                LONG ap = act;  // captured earlier in this block
                uintptr_t existing = 0;
                __try { existing = *(uintptr_t*)(handler + 0x170); } __except(EXCEPTION_EXECUTE_HANDLER) {}

                LONG64 panelSticky = InterlockedCompareExchange64(&g_panelStickyContainer[ap], 0, 0);
                LONG curBound = InterlockedCompareExchange(&g_currentBoundPanel, 0, 0);

                bool needClear = (existing >= 0x10000000000ULL) && (curBound != ap);
                if (needClear) {
                    __try {
                        *(uintptr_t*)(handler + 0x170) = 0;
                        Log("  Container bind: cleared stale 0x%llX (was bound to %s, now opening %s)",
                            (unsigned long long)existing,
                            (curBound >= 0 && curBound < PANEL_COUNT) ? g_panels[curBound].name : "?",
                            g_panels[ap].name);
                        existing = 0;
                    } __except(EXCEPTION_EXECUTE_HANDLER) {
                        Log("  Container bind: clear write EXCEPTION");
                    }
                }

                if (existing >= 0x10000000000ULL) {
                    Log("  Container bind: handler+0x170=0x%llX already correct for %s — keep",
                        (unsigned long long)existing, g_panels[ap].name);
                } else if (panelSticky && g_addrContainerVtable) {
                    bool valid = false;
                    __try {
                        valid = (*(uintptr_t*)(uintptr_t)panelSticky == g_addrContainerVtable);
                    } __except(EXCEPTION_EXECUTE_HANDLER) { valid = false; }
                    if (valid) {
                        __try {
                            *(uintptr_t*)(handler + 0x170) = (uintptr_t)panelSticky;
                            InterlockedExchange(&g_currentBoundPanel, ap);
                            Log("  Container bind: restored %s sticky 0x%llX",
                                g_panels[ap].name, (unsigned long long)panelSticky);
                        } __except(EXCEPTION_EXECUTE_HANDLER) {
                            Log("  Container bind: sticky write EXCEPTION");
                        }
                    } else {
                        Log("  Container bind: %s sticky 0x%llX stale (vtable mismatch) — clear",
                            g_panels[ap].name, (unsigned long long)panelSticky);
                        InterlockedExchange64(&g_panelStickyContainer[ap], 0);
                    }
                } else {
                    Log("  Container bind: %s has no sticky yet — letting game rebind via SetInventory",
                        g_panels[ap].name);
                }
        }
    }

    // Send an empty 0x15 command.  The 0x15 dispatch calls three virtual "prepare"
    // methods on sub-objects BEFORE iterating sub-commands.  With count=0 the
    // sub-command loop is skipped, so only the prepare calls run.
    if (g_fnHandler) {
        __try {
            uintptr_t sub1 = *(uintptr_t*)(handler + g_offPrepare1);
            uintptr_t sub2 = *(uintptr_t*)(handler + g_offPrepare2);
            uintptr_t sub3 = *(uintptr_t*)(handler + g_offPrepare3);
            if (sub1 > 0x10000 && sub2 > 0x10000 && sub3 > 0x10000) {
                uint8_t emptyPacket[24] = {};
                emptyPacket[0] = 0x15;
                typedef void (__fastcall *PFN_Handler)(void*, void*);
                ((PFN_Handler)g_fnHandler)((void*)handler, (void*)emptyPacket);
                Log("  Empty 0x15 sent (prepare calls triggered, offs=%X/%X/%X)",
                    g_offPrepare1, g_offPrepare2, g_offPrepare3);
            } else {
                Log("  Empty 0x15 SKIPPED (sub-objects null: %llX/%llX/%llX at offs %X/%X/%X)",
                    (unsigned long long)sub1,
                    (unsigned long long)sub2,
                    (unsigned long long)sub3,
                    g_offPrepare1, g_offPrepare2, g_offPrepare3);
            }
        } __except(EXCEPTION_EXECUTE_HANDLER) {
            Log("  Empty 0x15 EXCEPTION");
        }
    }

    // Explicitly hide the faction-donation sub-controller at +0x2E8 so the
    // Apr-23-default-visible "Donate Funds" keyguide disappears. This is the
    // symmetric counterpart to the game's own "show" call (FUN_140b999c0) that
    // SetDonationFaction uses on the success path — we're doing the opposite
    // for a no-faction private-storage open.
    if (g_fnHideSubCtrl) {
        __try {
            uintptr_t donationCtrl = *(uintptr_t*)(handler + g_offPrepare1);  // +0x2E8
            if (donationCtrl > 0x10000) {
                typedef void (__fastcall *PFN_Hide)(void*);
                ((PFN_Hide)g_fnHideSubCtrl)((void*)donationCtrl);
                Log("  Donation sub-controller hidden");
            }
        } __except(EXCEPTION_EXECUTE_HANDLER) {
            Log("  HideSubCtrl on donation EXCEPTION");
        }
    }

    // Load inventory items
    if (g_fnSetInventory) {
        typedef void (__fastcall *PFN_SetInv)(void*, void*);
        // SetInventory (FUN_140abc800 in Ghidra) iterates the panel slots and calls
        // vtable[0x20] (subscribe) for tokens ending in ",True" and vtable[0x28]
        // (unsubscribe) for ",False". When slot is already bound to namespace X,
        // calling subscribe again with namespace Y appears to be idempotent in
        // the slot's view-model — items don't refresh.
        //
        // Force a real refresh by sending an explicit unbind first (all tokens
        // with ",False"), then the real bind. This matches the natural flow at
        // a chest-NPC where the previous chest's binding is torn down before
        // the new one is set up.
        char unbindStr[256] = {};
        if (initString) {
            // Build a copy with ",True" / ",true" replaced by ",False".
            strncpy(unbindStr, initString, sizeof(unbindStr) - 1);
            for (char* p = unbindStr; *p; p++) {
                if ((p[0] == ',' || p[0] == ';') &&
                    (p[1] == 'T' || p[1] == 't') &&
                    (p[2] == 'R' || p[2] == 'r') &&
                    (p[3] == 'U' || p[3] == 'u') &&
                    (p[4] == 'E' || p[4] == 'e')) {
                    p[1] = 'F'; p[2] = 'a'; p[3] = 'l'; p[4] = 's';
                    // need a 6th char 'e' — extend the buffer in place
                    size_t len = strlen(p + 5);
                    memmove(p + 6, p + 5, len + 1);
                    p[5] = 'e';
                    p += 5;
                }
            }
        }
        __try {
            if (unbindStr[0]) {
                ((PFN_SetInv)g_fnSetInventory)((void*)handler, (void*)unbindStr);
                Log("  SetInventory unbind called (string=\"%s\")", unbindStr);
            }
            ((PFN_SetInv)g_fnSetInventory)((void*)handler, (void*)initString);
            Log("  SetInventory called (string=\"%s\")", initString ? initString : "");
        } __except(EXCEPTION_EXECUTE_HANDLER) {
            Log("  SetInventory EXCEPTION");
        }
    }

    // Fix bottom inventory label + top title
    if (g_fnSetTitle) {
        typedef uint8_t (__fastcall *PFN_SetTitle)(uintptr_t, const char*);
        PFN_SetTitle setTitle = (PFN_SetTitle)g_fnSetTitle;
        const char* title = GetWarehouseTitle();
        bool needUtf8Fix = !IsAscii(title);
        {
            LONG ap = InterlockedCompareExchange(&g_activePanel, 0, 0);
            if (ap < 0 || ap >= PANEL_COUNT) ap = PANEL_PRIVATE;
            Log("  Title selected: \"%s\" (active=%s)", title, g_panels[ap].name);
        }

        __try {
            uintptr_t bottomLabel = *(uintptr_t*)(handler + g_offBottomLabel);
            if (bottomLabel > 0x10000 && bottomLabel < 0x7FFFFFFFFFFF) {
                setTitle(bottomLabel, title);
                Log("  Bottom label (+0x%X) set: lang=%d needFix=%d",
                    g_offBottomLabel, GetGameLanguage(), needUtf8Fix);
                if (needUtf8Fix) {
                    bool fixed = SetTitleOnRenderer(bottomLabel, title, 0);
                    Log("  Bottom label UTF-8 fix: %s", fixed ? "OK" : "no renderer found");
                }
            } else {
                Log("  Bottom label (+0x%X) invalid pointer", g_offBottomLabel);
            }
        } __except(EXCEPTION_EXECUTE_HANDLER) {
            Log("  Bottom label (+0x%X) EXCEPTION", g_offBottomLabel);
        }

        __try {
            uintptr_t topNode = *(uintptr_t*)(handler + g_offTopTitle);
            if (topNode > 0x10000 && topNode < 0x7FFFFFFFFFFF) {
                uint8_t ret = setTitle(topNode, title);
                Log("  Top title (+0x%X) set: lang=%d ret=%u",
                    g_offTopTitle, GetGameLanguage(), (unsigned)ret);
                if (needUtf8Fix) {
                    bool fixed = SetTitleOnRenderer(topNode, title, 0);
                    Log("  Top title UTF-8 fix: %s", fixed ? "OK" : "no renderer found");
                }
            } else {
                Log("  Top title (+0x%X) invalid pointer — skipping", g_offTopTitle);
            }
        } __except(EXCEPTION_EXECUTE_HANDLER) {
            Log("  Top title (+0x%X) EXCEPTION", g_offTopTitle);
        }
    }
}

// ============================================================
//  F6 / Controller: Toggle Warehouse
// ============================================================
// ClearActivePanelState: hides a warehouse panel by replicating the game's 0x0f dispatcher
// logic without its unsafe scene-object lookup. Used by the F6-close path AND by the
// Switch-Key path — the latter reuses it to hide the current panel before re-initializing
// the other one. Does NOT touch mode bytes / g_warehouseActive — caller decides.
static void ClearActivePanelState(uintptr_t handler) {
    if (!handler) return;
    __try {
        // Part 1: clear active flag (handler+0x118) — what makes the panel vanish
        *(uint8_t*)(handler + g_offActiveFlag) = 0;
        // Part 2: clear panel value (handler+0x110) — what 0x0f clears last
        *(uint64_t*)(handler + 0x110) = 0;
        // Part 3: try to clear the scene-object render bit (equivalent to the
        // `*(uint8_t*)(scene+0x26A) &= 0xFE` step in 0x0f). Wrapped separately
        // so a missing scene object doesn't abort the clear.
        bool sceneBitCleared = false;
        __try {
            uintptr_t subObj = *(uintptr_t*)(handler + 0x8);
            if (subObj) {
                uintptr_t a8 = *(uintptr_t*)(subObj + 0xA8);
                if (a8) {
                    uintptr_t scene = *(uintptr_t*)(a8 + 0x10);
                    if (scene) {
                        *(uint8_t*)(scene + 0x26A) &= 0xFE;
                        sceneBitCleared = true;
                    }
                }
            }
        } __except(EXCEPTION_EXECUTE_HANDLER) {}
        Log("  Panel hidden (direct state clear, scene bit %s)",
            sceneBitCleared ? "cleared" : "skipped");
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        Log("  Panel hide direct cleanup EXCEPTION");
    }
}

static void TriggerWarehouse(bool fromKeyboard = false) {
    uintptr_t mainChar = (uintptr_t)InterlockedCompareExchange64(&g_mainChar, 0, 0);
    if (!mainChar) { Log("NOT READY: mainChar"); return; }

    uint8_t* mc = (uint8_t*)mainChar;

    if (!InterlockedCompareExchange(&g_warehouseActive, 0, 0)) {
        uint8_t curSub = mc[g_offSubByte];
        // Apr-23 safe sub-modes: 0x0D, 0x0F, 0x10 (gameplay variants). 0x0E between them
        // is "ingamemenu" — NOT a safe state for opening Private Storage.
        if (curSub != 0x0D && curSub != 0x0F && curSub != 0x10) {
            Log("BLOCKED: unsafe state (sub=0x%02X)", curSub);
            return;
        }

        LONG targetPanel = InterlockedExchange(&g_nextOpenPanel, PANEL_PRIVATE);
        {
            LONG tp = targetPanel;
            if (tp < 0 || tp >= PANEL_COUNT) tp = PANEL_PRIVATE;
            Log("=== OPENING WAREHOUSE (%s) ===", g_panels[tp].name);
        }
        InterlockedExchange(&g_activePanel, targetPanel);
        // Acquire spinlock for mode byte access (prevents race with game thread)
        while (InterlockedCompareExchange(&g_modeByteLock, 1, 0) != 0) { _mm_pause(); }
        memcpy(g_savedModes, mc + g_offModeFlags, 7);
        memcpy(g_savedSubtypes, mc + g_offSubtypes, 15);
        memset(mc + g_offModeFlags, 0, 7);
        memset(mc + g_offSubtypes, 0, 15);
        mc[g_offModeFlags + 4] = 1;
        mc[g_offSubtypes + 5] = 1;
        InterlockedExchange(&g_modeByteLock, 0);

        InterlockedExchange(&g_canShowSeen118, 0);
        InterlockedExchange64(&g_lastModalPassed, 0);
        InterlockedExchange(&g_warehouseActive, 1);
        g_openTimestamp = GetTickCount64();

        InterlockedExchange(&g_modeSwitchByMod, 1);

        // Try to initialize the panel immediately if handler is already captured.
        // On first F6 after loading a save, the handler is typically NULL here because
        // auto-capture happens in HookedCanShow which runs on the same (game) thread.
        // A blocking Sleep loop would prevent the game from processing frames and
        // calling CanShow, so the handler would never be captured.
        // Instead, we defer initialization via WM_INIT_WAREHOUSE — the game gets to
        // process a frame, CanShow fires, the handler is captured, and our deferred
        // message picks it up.
        uintptr_t handler = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);

        if (handler) {
            InitWarehousePanel(handler, GetInitStringForActive());
        } else {
            InterlockedExchange(&g_initRetryCount, 0);
            InterlockedExchange(&g_initPending, 1);
            Log("  Handler not yet captured — deferred init via InputThread");
        }

        Log("  Warehouse opened (mode=0x%02X sub=0x%02X)", mc[g_offModeByte], mc[g_offSubByte]);

    } else {
        // Block close while modal dialog is active (fixes F6 + controller toggle)
        if (IsNewModalDialogVisible()) {
            Log("CLOSE BLOCKED: modal dialog still active");
            return;
        }
        Log("=== CLOSING WAREHOUSE ===");
        InterlockedExchange(&g_warehouseActive, 0);
        InterlockedExchange(&g_initPending, 0);

        // Close only the currently-active panel. The other slot (if captured) keeps its
        // pointer for the next session — its +0x118 flag is already 0 because CanShow
        // suppressed it while inactive. See ClearActivePanelState for the 0x0f-replay logic.
        ClearActivePanelState((uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0));

        while (InterlockedCompareExchange(&g_modeByteLock, 1, 0) != 0) { _mm_pause(); }
        memcpy(mc + g_offModeFlags, g_savedModes, 7);
        memcpy(mc + g_offSubtypes, g_savedSubtypes, 15);
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

        InterlockedExchange(&g_modeSwitchByMod, 0);
        // Reset to Private so the next F6 opens Private (not whichever panel was last active).
        InterlockedExchange(&g_activePanel, PANEL_PRIVATE);
        // Forget which panel's container was bound — next open will rebind from sticky.
        InterlockedExchange(&g_currentBoundPanel, -1);

        Log("  Warehouse closed (mode=0x%02X sub=0x%02X)", mc[g_offModeByte], mc[g_offSubByte]);
    }
}

// ============================================================
//  Memory-Diff: capture handler-object snapshots before/after a regular chest-open
//  at the NPC, log which fields changed. Used to identify the container-bind writes
//  that the VM-protected dispatcher performs (since static decompilation is blocked).
// ============================================================
// Helper: log diff between two byte buffers, prefixing offset with the given label.
static void LogDiffRegion(const char* label, const uint8_t* before, const uint8_t* after, int size) {
    int totalChanged = 0;
    int runs = 0;
    for (int i = 0; i < size; ) {
        if (before[i] != after[i]) {
            int start = i;
            while (i < size && before[i] != after[i]) i++;
            int len = i - start;
            totalChanged += len;
            runs++;
            if (len == 1) {
                Log("  %s+0x%03X: u8  0x%02X -> 0x%02X",
                    label, start, before[start], after[start]);
            } else if (len == 2 && (start & 1) == 0) {
                Log("  %s+0x%03X: u16 0x%04X -> 0x%04X",
                    label, start, *(uint16_t*)&before[start], *(uint16_t*)&after[start]);
            } else if (len == 4 && (start & 3) == 0) {
                Log("  %s+0x%03X: u32 0x%08X -> 0x%08X",
                    label, start, *(uint32_t*)&before[start], *(uint32_t*)&after[start]);
            } else if (len == 8 && (start & 7) == 0) {
                Log("  %s+0x%03X: u64 0x%016llX -> 0x%016llX",
                    label, start,
                    (unsigned long long)*(uint64_t*)&before[start],
                    (unsigned long long)*(uint64_t*)&after[start]);
            } else {
                Log("  %s+0x%03X: run of %d bytes changed:", label, start, len);
                for (int j = 0; j < len; j++) {
                    Log("    %s+0x%03X: 0x%02X -> 0x%02X",
                        label, start + j, before[start + j], after[start + j]);
                }
            }
        } else {
            i++;
        }
    }
    Log("  %s total %d bytes changed in %d runs", label, totalChanged, runs);
}

// LookupInventoryTypeId: walk the global Inventory-Type hash-map (DAT_145f0da18)
// to resolve a 16-bit panel-ID for a given type-info pointer. Replicates the per-slot
// lookup logic from FUN_1415c1ae0 (which does this for all registered namespaces).
// Returns the resolved panel-ID, or 0xFFFF on failure.
//
// Layout of the hash-map at g_pInvTypeMap (offsets observed in FUN_1415c1ae0):
//   +0x60: u32 bucket count
//   +0x64: u32 total count (0 = empty)
//   +0x70: u8** buckets (each bucket is 0x100 bytes; first u32 = key count)
//   +0x78: u8** entries array (entry size = 8, target struct has hash@+4 and id@+6)
//
// The hash key for the lookup is the 16-bit truncation of the value at the type-info
// hash slot (e.g. *DAT_145e8f768 for Housing_GatheredMaterials).
// FindControllerInHeap: scan high-band heap for an object that has mainChar at
// +0x50 AND a non-NULL pointer at +0xa8 (matching FUN_140b99240's read pattern).
// Such objects are "ScriptControl"-style parents — exactly what the constructor
// needs as its second argument. Cached after first hit.
static volatile LONG64 g_cachedController = 0;

static uintptr_t FindControllerInHeap() {
    LONG64 cached = InterlockedCompareExchange64(&g_cachedController, 0, 0);
    if (cached) return (uintptr_t)cached;

    LONG64 mc = InterlockedCompareExchange64(&g_mainChar, 0, 0);
    if (!mc) return 0;
    uintptr_t mainChar = (uintptr_t)mc;

    uintptr_t scanBandLo = (mainChar & ~((uintptr_t)0xFFFFFFFFFFULL));
    uintptr_t scanBandHi = scanBandLo + 0x10000000000ULL;
    static constexpr uintptr_t MIN_HEAP_ADDR = 0x10000000000ULL;

    int hits = 0;
    uintptr_t firstHit = 0;
    uintptr_t scanned = 0;

    SYSTEM_INFO si;
    GetSystemInfo(&si);
    uintptr_t addr = scanBandLo;
    uintptr_t maxAddr = scanBandHi;
    if (maxAddr > (uintptr_t)si.lpMaximumApplicationAddress)
        maxAddr = (uintptr_t)si.lpMaximumApplicationAddress;

    DWORD t0 = GetTickCount();
    while (addr < maxAddr) {
        MEMORY_BASIC_INFORMATION mbi;
        if (!VirtualQuery((LPCVOID)addr, &mbi, sizeof(mbi))) break;
        bool ok = (mbi.State == MEM_COMMIT)
               && (mbi.Type == MEM_PRIVATE)
               && (mbi.Protect & (PAGE_READWRITE | PAGE_EXECUTE_READWRITE))
               && !(mbi.Protect & (PAGE_GUARD | PAGE_NOACCESS));
        if (ok && (uintptr_t)mbi.BaseAddress >= MIN_HEAP_ADDR) {
            uintptr_t base = (uintptr_t)mbi.BaseAddress;
            uintptr_t size = (uintptr_t)mbi.RegionSize;
            if (size > 0x10000000) size = 0x10000000;
            scanned += size;
            __try {
                // Object has +0x50 = mainChar AND +0xa8 = something heap-like.
                // Iterate p over object START addresses; check fields relative to p.
                for (uintptr_t p = base; p + 0x150 <= base + size; p += 8) {
                    if (*(uintptr_t*)(p + 0x50) == mainChar) {
                        uintptr_t f_a8 = *(uintptr_t*)(p + 0xa8);
                        if (f_a8 >= MIN_HEAP_ADDR) {
                            if (!firstHit) firstHit = p;
                            hits++;
                            if (hits >= 8) break;
                        }
                    }
                }
            } __except(EXCEPTION_EXECUTE_HANDLER) {}
        }
        addr = (uintptr_t)mbi.BaseAddress + mbi.RegionSize;
        if (hits >= 8) break;
        if ((GetTickCount() - t0) > 5000) {
            Log("  Controller scan: timeout 5s, scanned=%lluMB hits=%d",
                (unsigned long long)(scanned / (1024 * 1024)), hits);
            break;
        }
    }

    Log("  Controller scan: scanned=%lluMB, hits=%d, firstHit=0x%llX (mainChar=0x%llX)",
        (unsigned long long)(scanned / (1024 * 1024)), hits,
        (unsigned long long)firstHit, (unsigned long long)mainChar);

    if (firstHit) {
        InterlockedExchange64(&g_cachedController, (LONG64)firstHit);
        return firstHit;
    }
    return 0;
}

// FindSingletonInHeap (dead code — kept for reference). Was used in an early
// iteration that scanned for the FactorySingleton via vtable-pointer match.
// Replaced by the factory-entry hook (CaptureOnFactory), which gets the real
// singleton + ctrl with no scanning. Compiler may warn; harmless.
static volatile LONG64 g_cachedSingleton = 0;

static uintptr_t FindSingletonInHeap() {
    LONG64 cached = InterlockedCompareExchange64(&g_cachedSingleton, 0, 0);
    if (cached) return (uintptr_t)cached;
    if (!g_addrFactorySingletonVt) return 0;

    // Anchor scan range to mainChar's address (a known game-heap pointer).
    // Game heap on Win10/11 lives in the high terabyte range (e.g. 0x5_3000_0000_0000).
    // Low-address regions like RTTI tables, system DLL data, etc. can spuriously
    // contain a copy of the vtable pointer — exclude them by requiring a hit
    // address > 0x10_0000_0000 (1 TB) AND in the same 16-TB band as mainChar.
    LONG64 mc = InterlockedCompareExchange64(&g_mainChar, 0, 0);
    if (!mc) {
        Log("  Heap scan: mainChar not yet resolved — skip");
        return 0;
    }
    uintptr_t mainChar    = (uintptr_t)mc;
    uintptr_t scanBandLo  = (mainChar & ~((uintptr_t)0xFFFFFFFFFFULL));  // 1 TB-aligned floor
    uintptr_t scanBandHi  = scanBandLo + 0x10000000000ULL;               // +16 TB ceiling
    static constexpr uintptr_t MIN_HEAP_ADDR = 0x10000000000ULL;          // 1 TB threshold

    uintptr_t target = g_addrFactorySingletonVt;
    uintptr_t scanned = 0;
    int hits = 0;
    uintptr_t firstHit = 0;

    SYSTEM_INFO si;
    GetSystemInfo(&si);
    uintptr_t addr = scanBandLo;
    uintptr_t maxAddr = scanBandHi;
    if (maxAddr > (uintptr_t)si.lpMaximumApplicationAddress)
        maxAddr = (uintptr_t)si.lpMaximumApplicationAddress;

    DWORD t0 = GetTickCount();
    while (addr < maxAddr) {
        MEMORY_BASIC_INFORMATION mbi;
        if (!VirtualQuery((LPCVOID)addr, &mbi, sizeof(mbi))) break;
        // Heap pages are MEM_COMMIT + MEM_PRIVATE + PAGE_READWRITE, large RegionSize.
        bool ok = (mbi.State == MEM_COMMIT)
               && (mbi.Type == MEM_PRIVATE)
               && (mbi.Protect & (PAGE_READWRITE | PAGE_EXECUTE_READWRITE))
               && !(mbi.Protect & (PAGE_GUARD | PAGE_NOACCESS));
        // Additional filter: only scan regions in the high heap band.
        if (ok && (uintptr_t)mbi.BaseAddress >= MIN_HEAP_ADDR) {
            uintptr_t base = (uintptr_t)mbi.BaseAddress;
            uintptr_t size = (uintptr_t)mbi.RegionSize;
            if (size > 0x10000000) size = 0x10000000;  // cap 256 MiB per region
            scanned += size;
            __try {
                for (uintptr_t p = base; p + 8 <= base + size; p += 8) {
                    if (*(uintptr_t*)p == target && p >= MIN_HEAP_ADDR) {
                        if (!firstHit) firstHit = p;
                        hits++;
                        if (hits >= 16) break;
                    }
                }
            } __except(EXCEPTION_EXECUTE_HANDLER) {}
        }
        addr = (uintptr_t)mbi.BaseAddress + mbi.RegionSize;
        if (hits >= 16) break;
        if ((GetTickCount() - t0) > 5000) {
            Log("  Heap scan: timeout after 5s (mainChar-anchored), scanned=0x%llX hits=%d",
                (unsigned long long)scanned, hits);
            break;
        }
    }

    Log("  Heap scan: scanned=%llu MiB, vtable-hits=%d, firstHit=0x%llX (band 0x%llX..0x%llX, mainChar=0x%llX)",
        (unsigned long long)(scanned / (1024 * 1024)), hits,
        (unsigned long long)firstHit,
        (unsigned long long)scanBandLo, (unsigned long long)scanBandHi,
        (unsigned long long)mainChar);

    if (firstHit) {
        InterlockedExchange64(&g_cachedSingleton, (LONG64)firstHit);
        return firstHit;
    }
    return 0;
}

// TryCreateContainerViaSingleton: build a Gatherables-Chest container by
// calling the factory directly. The factory chain is:
//
//   FUN_14a9edc10(owner, init) {
//     buf = alloc(0x8f8, 0x10);
//     FUN_140c910d0(buf, init);          // 2-arg constructor
//     buf+0x18 = owner+0x10 (uint32);
//     buf+0x1c = owner+0x88 (uint8);
//   }
//
//   FUN_140c910d0(buf, init) {
//     FUN_140b99240(buf+0xN, init);      // base init
//     ... more init ...
//   }
//
//   FUN_140b99240(out, ctrl) reads ctrl+0x50, ctrl+0xa8, ctrl+0x148, ctrl+0x150 —
//   so init MUST be a "Controller" object with those fields populated.
//
// Strategy: pass the captured warehouse handler as `init`. Root-style UI panels
// have controller-like field layout (mainChar at +0x50, subs etc). For `owner`
// we use a synthetic stub with only +0x10 and +0x88 set (those are the only
// fields the factory itself reads). All wrapped in SEH; on crash we abort.
static uintptr_t TryCreateContainerViaSingleton(uintptr_t handler) {
    if (!g_addrFactoryWrapper || !g_addrSingletonTypeIdSlot) return 0;
    if (!handler) return 0;

    typedef uintptr_t (__fastcall *PFN_Factory)(uintptr_t owner, uintptr_t init_arg);

    // Prefer args captured by our factory hook (real, fully-init game objects)
    // over the synthetic fake-owner / heap-scanned fallback. The captured
    // singleton stays valid for the rest of the session once the game has
    // called it once (e.g. user walked near the chest at any earlier time).
    uintptr_t realOwner = (uintptr_t)InterlockedCompareExchange64(&g_capturedFactorySingleton, 0, 0);
    uintptr_t realCtrl  = (uintptr_t)InterlockedCompareExchange64(&g_capturedFactoryCtrl,      0, 0);
    bool useCaptured = (realOwner >= 0x10000000000ULL && realCtrl >= 0x10000000000ULL);

    alignas(16) uint8_t fakeOwner[0x100] = {};
    *(uint32_t*)(fakeOwner + 0x10) = *(uint32_t*)g_addrSingletonTypeIdSlot;
    *(uint8_t *)(fakeOwner + 0x88) = 0x00;

    uintptr_t container = 0;
    __try {
        uintptr_t owner = useCaptured ? realOwner : (uintptr_t)fakeOwner;
        uintptr_t ctrl  = 0;
        if (useCaptured) {
            ctrl = realCtrl;
            Log("  Factory path: using CAPTURED args owner=0x%llX ctrl=0x%llX",
                (unsigned long long)owner, (unsigned long long)ctrl);
        } else {
            ctrl = FindControllerInHeap();
            if (!ctrl) {
                Log("  Factory path: no Controller in heap and nothing captured "
                    "— abort (walk near a housing chest first to populate)");
                return 0;
            }
            Log("  Factory path: SYNTHESIZED owner + scanned ctrl=0x%llX (typeId=0x%08X) "
                "— may be incomplete; captured path preferred",
                (unsigned long long)ctrl, *(uint32_t*)(fakeOwner + 0x10));
        }
        container = ((PFN_Factory)g_addrFactoryWrapper)(owner, ctrl);
        if (container) {
            Log("  Factory path: returned container=0x%llX",
                (unsigned long long)container);
            uintptr_t vt = *(uintptr_t*)container;
            if (vt != g_addrContainerVtable) {
                Log("  Factory path: WARNING — container vtable=0x%llX (expected 0x%llX)",
                    (unsigned long long)vt, (unsigned long long)g_addrContainerVtable);
            }

            // Post-construction patch: populate the fields the real NPC-open
            // code path sets but which our factory call leaves at 0. Values
            // from the captured diff (cont was a real GC container after NPC):
            //   cont+0x020 = handler back-reference
            //   cont+0x084 = 0xFFFFFFFF (sentinel?)
            //   cont+0x09C = 0x06D6 (capacity, observed)
            //   cont+0x0A0 = 0x06D6 (max-slots-like)
            //   cont+0x0B8 = 1 (some flag)
            // Array fields cont+0x048/0x058/0x068 (heap arrays) are intentionally
            // left at 0 — populating them with stale pointers would crash. UI may
            // tolerate empty/null arrays; if not we'll know from next test.
            *(uintptr_t*)(container + 0x020) = handler;
            *(uint32_t* )(container + 0x084) = 0xFFFFFFFF;
            *(uint32_t* )(container + 0x09C) = 0x06D6;
            *(uint32_t* )(container + 0x0A0) = 0x06D6;
            *(uint32_t* )(container + 0x0B8) = 1;
            Log("  Factory path: patched cont+0x20=handler, cont+0x9C/0xA0=0x06D6, cont+0xB8=1");
        } else {
            Log("  Factory path: factory returned NULL");
        }
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        Log("  Factory path: EXCEPTION (Controller candidate had unexpected layout) — "
            "clear cache, will rescan next time");
        InterlockedExchange64(&g_cachedController, 0);
        return 0;
    }

    return container;
}

// ResolveContainerForPanelId: walk sub->0x50->0xb0->0xd8 to get the global container
// array, then index it by panelId. Returns the container pointer at that slot,
// or 0 on failure / out-of-range.
static uintptr_t ResolveContainerForPanelId(uintptr_t handler, uint16_t panelId) {
    if (!handler) return 0;
    __try {
        uintptr_t sub = *(uintptr_t*)(handler + 0x8);
        if (!sub) return 0;
        uintptr_t lvl1 = *(uintptr_t*)(sub + 0x50);
        if (!lvl1) return 0;
        uintptr_t lvl2 = *(uintptr_t*)(lvl1 + 0xb0);
        if (!lvl2) return 0;
        uintptr_t arrStruct = *(uintptr_t*)(lvl2 + 0xd8);
        if (!arrStruct) return 0;
        uintptr_t arrPtr = *(uintptr_t*)arrStruct;
        uint32_t arrCnt = *(uint32_t*)(arrStruct + 8);
        if (!arrPtr || (uint32_t)panelId >= arrCnt) return 0;
        return *(uintptr_t*)(arrPtr + (uintptr_t)panelId * 8);
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        return 0;
    }
}

// LookupInventoryTypeId: call the game's own type-name → 16-bit ID resolver.
// pStringSlot is the address of an 8-byte slot that holds a pointer to the canonical
// game string (e.g. "Housing_GatheredMaterials" stored by the namespace setup function).
static uint16_t LookupInventoryTypeId(uintptr_t pStringSlot) {
    if (!pStringSlot || !g_fnTypeNameLookup) {
        Log("  Lookup: pStringSlot=0x%llX fn=0x%llX",
            (unsigned long long)pStringSlot, (unsigned long long)g_fnTypeNameLookup);
        return 0xFFFF;
    }
    __try {
        // FUN_1402ffe80 returns a pointer to a String-wrapper struct: { char* data; ... }
        // So pStringSlot → wrapper-ptr → wrapper[0] → actual string.
        char** wrapper = *(char***)pStringSlot;
        if (!wrapper) {
            Log("  Lookup: wrapper pointer is NULL — setup not yet run?");
            return 0xFFFF;
        }
        char* str = wrapper[0];
        if (!str) {
            Log("  Lookup: string pointer (wrapper[0]) is NULL");
            return 0xFFFF;
        }
        char preview[40] = {};
        for (int i = 0; i < 39 && str[i]; i++) preview[i] = str[i];
        Log("  Lookup: calling resolver with str=\"%s\"", preview);

        short outId = (short)0xFF;  // sentinel
        typedef int (__fastcall *PFN_Resolver)(char*, short*);
        int rc = ((PFN_Resolver)g_fnTypeNameLookup)(str, &outId);
        Log("  Lookup: resolver returned rc=%d, outId=0x%04X", rc, (unsigned)(uint16_t)outId);

        if (rc == 0 || outId == (short)0xFF) return 0xFFFF;
        return (uint16_t)outId;
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        Log("  Lookup: EXCEPTION");
        return 0xFFFF;
    }
}

// Resolve the cached Gatherables panel-ID via the Inventory-Type hash-map lookup.
// Idempotent — caches the result; returns 0xFFFF on failure.
static uint16_t GetGatherablesPanelId() {
    LONG cached = InterlockedCompareExchange(&g_resolvedGatherablesId, 0, 0);
    if (cached > 0) return (uint16_t)cached;
    if (cached < 0) return 0xFFFF;  // previous lookup failed, don't retry

    uint16_t id = LookupInventoryTypeId(g_pHGMStringSlot);
    if (id == 0xFFFF || id == 0) {
        InterlockedExchange(&g_resolvedGatherablesId, -1);
        Log("Gatherables panel-id lookup FAILED (hash-map not yet populated?)");
        return 0xFFFF;
    }
    InterlockedExchange(&g_resolvedGatherablesId, (LONG)id);
    Log("Gatherables panel-id resolved via hash-map: 0x%04X", id);
    return id;
}

// Per-panel resolved type-id cache. Filled lazily on first lookup. 0 = not
// yet resolved, -1 = resolution failed (don't retry every open).
static volatile LONG g_resolvedPanelId[PANEL_COUNT] = {};

// Extract the second token of a panel's InitString — that's the namespace
// name the game's hash-map maps to a 2-byte type-id (e.g. "Housing_Dresser"
// from "Character,Focus,True;Housing_Dresser,Focus,True"). Writes up to
// dstSize-1 chars + NUL into dst. Returns false if the string can't be parsed.
static bool ExtractPanelNamespace(const char* initString, char* dst, size_t dstSize) {
    if (!initString || !dst || dstSize < 2) return false;
    // Skip the first token ("Character,Focus,True") up to the first ';'.
    const char* p = strchr(initString, ';');
    if (!p) return false;
    p++;
    // Copy until ',' or end-of-string.
    size_t i = 0;
    while (*p && *p != ',' && i + 1 < dstSize) dst[i++] = *p++;
    dst[i] = '\0';
    return i > 0;
}

// Resolve a panel's type-id by feeding the namespace string from its
// InitString into the same resolver used for Gatherables. Idempotent —
// caches per-panel; returns 0xFFFF on failure.
static uint16_t GetPanelTypeId(int panelIdx) {
    if (panelIdx < 0 || panelIdx >= PANEL_COUNT) return 0xFFFF;
    if (panelIdx == PANEL_GATHERABLES) return GetGatherablesPanelId();

    LONG cached = InterlockedCompareExchange(&g_resolvedPanelId[panelIdx], 0, 0);
    if (cached > 0) return (uint16_t)cached;
    if (cached < 0) return 0xFFFF;

    if (!g_fnTypeNameLookup) return 0xFFFF;

    char ns[64] = {};
    if (!ExtractPanelNamespace(g_panels[panelIdx].initString, ns, sizeof(ns))) {
        Log("  Lookup: can't extract namespace from InitString for panel %s",
            g_panels[panelIdx].name);
        InterlockedExchange(&g_resolvedPanelId[panelIdx], -1);
        return 0xFFFF;
    }

    __try {
        Log("  Lookup: calling resolver with str=\"%s\" (panel %s)",
            ns, g_panels[panelIdx].name);
        short outId = (short)0xFF;
        typedef int (__fastcall *PFN_Resolver)(char*, short*);
        int rc = ((PFN_Resolver)g_fnTypeNameLookup)(ns, &outId);
        Log("  Lookup: resolver returned rc=%d, outId=0x%04X", rc, (unsigned)(uint16_t)outId);
        if (rc == 0 || outId == (short)0xFF) {
            InterlockedExchange(&g_resolvedPanelId[panelIdx], -1);
            Log("Panel %s type-id lookup FAILED", g_panels[panelIdx].name);
            return 0xFFFF;
        }
        InterlockedExchange(&g_resolvedPanelId[panelIdx], (LONG)(uint16_t)outId);
        Log("Panel %s type-id resolved: 0x%04X", g_panels[panelIdx].name, (uint16_t)outId);
        return (uint16_t)outId;
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        Log("  Lookup: EXCEPTION for panel %s", g_panels[panelIdx].name);
        InterlockedExchange(&g_resolvedPanelId[panelIdx], -1);
        return 0xFFFF;
    }
}

// WalkContainerChain: replicates FUN_14354b520's logic. Walks sub->0x60 chain until
// reaching a terminal sub-object (sub->0xa8 == 0 OR sub->0xa8->8 == 0), then reads
// panel-ID from terminal+0x92 and looks up the container in the global array.
// Logs each step so we can see what panel-IDs the game uses for different chests.
static void WalkAndLogChain(uintptr_t handler, const char* label) {
    __try {
        uintptr_t sub = *(uintptr_t*)(handler + 0x8);
        Log("  [%s] handler=0x%llX sub=0x%llX", label,
            (unsigned long long)handler, (unsigned long long)sub);
        if (!sub) { Log("  [%s] sub is NULL", label); return; }

        uintptr_t cur = sub;
        int hops = 0;
        while (hops < 8) {
            uintptr_t a8 = *(uintptr_t*)(cur + 0xa8);
            uintptr_t a8_p8 = a8 ? *(uintptr_t*)(a8 + 0x8) : 0;
            uint16_t pid = *(uint16_t*)(cur + 0x92);
            Log("  [%s] hop=%d cur=0x%llX panelId=0x%04X sub+0xa8=0x%llX sub+0xa8+8=0x%llX",
                label, hops, (unsigned long long)cur, pid,
                (unsigned long long)a8, (unsigned long long)a8_p8);
            if (a8 == 0 || a8_p8 == 0) {
                // Terminal — do container lookup
                uintptr_t lvl1 = *(uintptr_t*)(cur + 0x50);
                if (!lvl1) { Log("  [%s] terminal: cur+0x50 is NULL", label); return; }
                uintptr_t lvl2 = *(uintptr_t*)(lvl1 + 0xb0);
                if (!lvl2) { Log("  [%s] terminal: cur+0x50+0xb0 is NULL", label); return; }
                uintptr_t arr = *(uintptr_t*)(lvl2 + 0xd8);
                if (!arr) { Log("  [%s] terminal: cur+0x50+0xb0+0xd8 is NULL", label); return; }
                uintptr_t arrPtr = *(uintptr_t*)arr;
                uint32_t arrCnt = *(uint32_t*)(arr + 8);
                Log("  [%s] container array @ 0x%llX (count=%u)",
                    label, (unsigned long long)arr, arrCnt);
                if (pid != 0xFFFF && pid < arrCnt) {
                    uintptr_t containerPtr = *(uintptr_t*)(arrPtr + (uintptr_t)pid * 8);
                    Log("  [%s] CONTAINER for panelId 0x%04X = 0x%llX",
                        label, pid, (unsigned long long)containerPtr);
                } else {
                    Log("  [%s] panelId 0x%04X out of range (count=%u)", label, pid, arrCnt);
                }
                return;
            }
            cur = *(uintptr_t*)(cur + 0x60);
            if (!cur) { Log("  [%s] sub+0x60 chain ended at hop %d (NULL)", label, hops); return; }
            hops++;
        }
        Log("  [%s] chain too deep (>8 hops), aborting", label);
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        Log("  [%s] EXCEPTION during chain walk", label);
    }
}

static void DoDiffSnapshot() {
    uintptr_t handler = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);
    if (!handler) {
        Log("DIFF: no handler captured yet — open the warehouse once with F6 first");
        return;
    }
    LONG state = InterlockedCompareExchange(&g_snapshotState, 0, 0);
    if (state == 0) {
        Log("DIFF: BEFORE — chain walk:");
        WalkAndLogChain(handler, "BEFORE");
        __try {
            memcpy(g_snapshotBefore, (void*)handler, HANDLER_SNAPSHOT_SIZE);
            // Snapshot the container object pointed to by handler+0x170 (if non-NULL).
            uintptr_t contBefore = *(uintptr_t*)(handler + 0x170);
            InterlockedExchange64(&g_contBeforeAddr, (LONG64)contBefore);
            if (contBefore > 0x10000 && contBefore < 0x7FFFFFFFFFFFULL) {
                memcpy(g_contSnapshotBefore, (void*)contBefore, CONT_SNAPSHOT_SIZE);
                Log("DIFF: container ptr at handler+0x170 = 0x%llX (snapshotted)",
                    (unsigned long long)contBefore);
            } else {
                memset(g_contSnapshotBefore, 0, CONT_SNAPSHOT_SIZE);
                Log("DIFF: handler+0x170 = 0x%llX (NULL or invalid, skipped)",
                    (unsigned long long)contBefore);
            }
            uintptr_t sub = *(uintptr_t*)(handler + 0x8);
            if (sub > 0x10000 && sub < 0x7FFFFFFFFFFFULL) {
                memcpy(g_subSnapshotBefore, (void*)sub, SUB_SNAPSHOT_SIZE);
                InterlockedExchange64(&g_subSnapshotAddr, (LONG64)sub);
                Log("DIFF: BEFORE snapshot captured (handler=0x%llX, sub=0x%llX). Now go open the chest regularly, then press the hotkey again.",
                    (unsigned long long)handler, (unsigned long long)sub);
            } else {
                InterlockedExchange64(&g_subSnapshotAddr, 0);
                Log("DIFF: BEFORE snapshot captured (handler=0x%llX, sub-object missing/invalid). Go open the chest, press the hotkey again.",
                    (unsigned long long)handler);
            }
            InterlockedExchange(&g_snapshotState, 1);
        } __except(EXCEPTION_EXECUTE_HANDLER) {
            Log("DIFF: BEFORE snapshot read EXCEPTION");
        }
        return;
    }
    // state == 1 → capture after + diff
    Log("DIFF: AFTER — chain walk:");
    WalkAndLogChain(handler, "AFTER");
    __try {
        memcpy(g_snapshotAfter, (void*)handler, HANDLER_SNAPSHOT_SIZE);
        Log("DIFF: AFTER snapshot captured (handler=0x%llX). Computing changes:",
            (unsigned long long)handler);
        LogDiffRegion("handler", g_snapshotBefore, g_snapshotAfter, HANDLER_SNAPSHOT_SIZE);

        // Container-object diff
        uintptr_t contBefore = (uintptr_t)InterlockedCompareExchange64(&g_contBeforeAddr, 0, 0);
        uintptr_t contAfter  = *(uintptr_t*)(handler + 0x170);
        InterlockedExchange64(&g_contAfterAddr, (LONG64)contAfter);
        Log("  container: before=0x%llX after=0x%llX",
            (unsigned long long)contBefore, (unsigned long long)contAfter);
        if (contAfter > 0x10000 && contAfter < 0x7FFFFFFFFFFFULL) {
            memcpy(g_contSnapshotAfter, (void*)contAfter, CONT_SNAPSHOT_SIZE);

            // Scan the global container array for this pointer to find its index.
            __try {
                uintptr_t sub = *(uintptr_t*)(handler + 0x8);
                uintptr_t lvl1 = sub ? *(uintptr_t*)(sub + 0x50) : 0;
                uintptr_t lvl2 = lvl1 ? *(uintptr_t*)(lvl1 + 0xb0) : 0;
                uintptr_t arrStruct = lvl2 ? *(uintptr_t*)(lvl2 + 0xd8) : 0;
                if (arrStruct) {
                    uintptr_t arrPtr = *(uintptr_t*)arrStruct;
                    uint32_t arrCnt = *(uint32_t*)(arrStruct + 8);
                    int found = -1;
                    for (uint32_t i = 0; i < arrCnt; i++) {
                        if (*(uintptr_t*)(arrPtr + (uintptr_t)i * 8) == contAfter) {
                            found = (int)i;
                            break;
                        }
                    }
                    if (found >= 0) {
                        Log("  container: NPC container 0x%llX is at array index 0x%04X (=%d)",
                            (unsigned long long)contAfter, found, found);
                    } else {
                        Log("  container: NPC container 0x%llX NOT in global array (count=%u) — different lookup mechanism",
                            (unsigned long long)contAfter, arrCnt);
                    }
                }
            } __except(EXCEPTION_EXECUTE_HANDLER) {}

            if (contBefore == contAfter) {
                Log("  container: same pointer, comparing contents:");
                LogDiffRegion("container", g_contSnapshotBefore, g_contSnapshotAfter, CONT_SNAPSHOT_SIZE);
            } else {
                Log("  container: POINTER CHANGED — dumping new container's first 0x100 bytes:");
                for (int i = 0; i < 0x100; i += 0x10) {
                    Log("    cont+0x%03X: %02X %02X %02X %02X %02X %02X %02X %02X  %02X %02X %02X %02X %02X %02X %02X %02X",
                        i,
                        g_contSnapshotAfter[i+0], g_contSnapshotAfter[i+1],
                        g_contSnapshotAfter[i+2], g_contSnapshotAfter[i+3],
                        g_contSnapshotAfter[i+4], g_contSnapshotAfter[i+5],
                        g_contSnapshotAfter[i+6], g_contSnapshotAfter[i+7],
                        g_contSnapshotAfter[i+8], g_contSnapshotAfter[i+9],
                        g_contSnapshotAfter[i+10], g_contSnapshotAfter[i+11],
                        g_contSnapshotAfter[i+12], g_contSnapshotAfter[i+13],
                        g_contSnapshotAfter[i+14], g_contSnapshotAfter[i+15]);
                }
            }
        } else {
            Log("  container: handler+0x170 = 0x%llX (NULL or invalid)",
                (unsigned long long)contAfter);
        }

        // Sub-object diff — read the current sub pointer and compare against the one
        // we captured before. If the pointer changed, the sub-object itself was
        // re-bound, which is a strong signal in itself.
        uintptr_t subBefore = (uintptr_t)InterlockedCompareExchange64(&g_subSnapshotAddr, 0, 0);
        uintptr_t subAfter = *(uintptr_t*)(handler + 0x8);
        if (subBefore == 0 || subAfter == 0) {
            Log("  sub: skipped (before=0x%llX, after=0x%llX — one or both invalid)",
                (unsigned long long)subBefore, (unsigned long long)subAfter);
        } else if (subBefore != subAfter) {
            Log("  sub: POINTER CHANGED before=0x%llX after=0x%llX (re-bound)",
                (unsigned long long)subBefore, (unsigned long long)subAfter);
            memcpy(g_subSnapshotAfter, (void*)subAfter, SUB_SNAPSHOT_SIZE);
            // Diff the *new* sub-object against zero baseline (since pointer changed,
            // before/after of the same address would be meaningless)
            for (int i = 0; i < SUB_SNAPSHOT_SIZE; i++) g_subSnapshotBefore[i] = 0;
            LogDiffRegion("sub(NEW)", g_subSnapshotBefore, g_subSnapshotAfter, SUB_SNAPSHOT_SIZE);
        } else {
            memcpy(g_subSnapshotAfter, (void*)subAfter, SUB_SNAPSHOT_SIZE);
            Log("  sub: same pointer 0x%llX, comparing contents:", (unsigned long long)subAfter);
            LogDiffRegion("sub", g_subSnapshotBefore, g_subSnapshotAfter, SUB_SNAPSHOT_SIZE);
        }

        InterlockedExchange(&g_snapshotState, 0);
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        Log("DIFF: AFTER snapshot read EXCEPTION");
        InterlockedExchange(&g_snapshotState, 0);
    }
}

// ============================================================
//  WndProc + Input
// ============================================================
static volatile LONG g_pendingCircleClose = 0;  // 1 = waiting for Circle release to close

static LRESULT CALLBACK HookedWndProc(HWND h, UINT m, WPARAM w, LPARAM l) {
    if (m==WM_TRIGGER_WAREHOUSE) { TriggerWarehouse((bool)w); return 0; }
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

        // Per-panel PSButton rising edges → toggle that panel
        for (int i = 0; i < PANEL_COUNT; i++) {
            if (g_panels[i].psButtonByteOff < 0) {
                g_panelPsLastDown[i] = false;
                continue;
            }
            bool down = g_panelPsCurrentDown[i];
            if (down && !g_panelPsLastDown[i]) {
                if (InterlockedCompareExchange(&g_warehouseActive, 0, 0)) {
                    if (IsNewModalDialogVisible()) {
                        Log("Panel %s PS button → sub-dialog active, ignoring",
                            g_panels[i].name);
                    } else {
                        Log("Panel %s PS button → closing warehouse",
                            g_panels[i].name);
                        PostMessageA(h, WM_TRIGGER_WAREHOUSE, 1, 0);
                    }
                } else {
                    Log("Panel %s PS button → opening", g_panels[i].name);
                    InterlockedExchange(&g_nextOpenPanel, i);
                    PostMessageA(h, WM_TRIGGER_WAREHOUSE, 0, 0);
                }
            }
            g_panelPsLastDown[i] = down;
        }

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

        // DiffSnapshotKey — must be available regardless of safe-state, because the
        // chest UI puts the player into a non-safe sub-mode and would skip otherwise.
        static bool diffKeyDownGlobal = false;
        if (g_diffSnapshotKey) {
            bool d = (GetAsyncKeyState(g_diffSnapshotKey) & 0x8000) != 0;
            bool modOk = (g_diffSnapshotModifier == 0) || (GetAsyncKeyState(g_diffSnapshotModifier) & 0x8000) != 0;
            if (d && modOk && !diffKeyDownGlobal) {
                diffKeyDownGlobal = true;
                DWORD now = GetTickCount();
                if (now - g_lastAct >= 400) {
                    g_lastAct = now;
                    DoDiffSnapshot();
                }
            } else if (!d) diffKeyDownGlobal = false;
        }

        // Lazy-resolve mainChar from singleton if not yet captured
        if (!InterlockedCompareExchange64(&g_mainChar, 0, 0)) {
            uintptr_t resolved = ResolveMainChar();
            if (resolved > 0x10000000000ULL) {
                InterlockedExchange64(&g_mainChar, (LONG64)resolved);
                Log("mainChar: 0x%llX (singleton, deferred)", (unsigned long long)resolved);
            }
        }

        // Sticky-binding poller for handler+0x170. When the warehouse handler is
        // captured AND the game has written a fully-init container pointer there
        // (because the player is near the GC chest and the chest is loaded),
        // remember it. We use it later in the F7-far-away path to repopulate
        // handler+0x170 after the game has zeroed it.
        //
        // GUARD: only save while warehouse is actively shown. After CLOSE, the
        // close path resets g_activePanel = PANEL_PRIVATE but handler+0x170 may
        // still hold the previous panel's container — saving here would mis-
        // attribute that container to Private and corrupt Private's sticky.
        if (InterlockedCompareExchange(&g_warehouseActive, 0, 0)) {
            uintptr_t handler = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);
            if (handler) {
                __try {
                    uintptr_t cont = *(uintptr_t*)(handler + 0x170);
                    if (cont >= 0x10000000000ULL && g_addrContainerVtable) {
                        uintptr_t vt = *(uintptr_t*)cont;
                        if (vt == g_addrContainerVtable) {
                            // Save into the slot for whichever panel is active right now —
                            // the game just bound this container in response to our open
                            // sequence, so it belongs to that panel.
                            LONG ap = InterlockedCompareExchange(&g_activePanel, 0, 0);
                            if (ap < 0 || ap >= PANEL_COUNT) ap = PANEL_PRIVATE;
                            LONG64 prev = InterlockedCompareExchange64(&g_panelStickyContainer[ap], 0, 0);
                            if (prev != (LONG64)cont) {
                                uint32_t typeId  = *(uint32_t*)(cont + 0x18);
                                uint32_t cap1    = *(uint32_t*)(cont + 0x9C);
                                uint32_t cap2    = *(uint32_t*)(cont + 0xA0);
                                uintptr_t arr1   = *(uintptr_t*)(cont + 0x48);
                                uintptr_t arr2   = *(uintptr_t*)(cont + 0x58);
                                InterlockedExchange64(&g_panelStickyContainer[ap], (LONG64)cont);
                                InterlockedExchange(&g_currentBoundPanel, ap);
                                Log("Sticky bind [%s]: saved 0x%llX type=0x%X cap=%u/%u arr1=0x%llX arr2=0x%llX",
                                    g_panels[ap].name, (unsigned long long)cont, typeId, cap1, cap2,
                                    (unsigned long long)arr1, (unsigned long long)arr2);
                            }
                        }
                    }
                } __except(EXCEPTION_EXECUTE_HANDLER) {}
            }
        }

        // Deferred warehouse init: handler wasn't available when F6 was pressed.
        // We poll from this thread (16ms interval) because PostMessage from WndProc
        // re-queues before the game renders a frame.  InputThread is a separate thread
        // so the game processes frames between our checks.
        if (InterlockedCompareExchange(&g_initPending, 0, 0)) {
            uintptr_t handler = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);
            if (handler) {
                InterlockedExchange(&g_initPending, 0);
                PostMessageA(g_gameWindow, WM_INIT_WAREHOUSE, 0, 0);
            } else {
                LONG retries = InterlockedIncrement(&g_initRetryCount);
                if (retries >= 60) {  // ~1 second at 16ms
                    InterlockedExchange(&g_initPending, 0);
                    Log("  Deferred init: GAVE UP after %ld retries", retries);
                }
            }
        }

        // Read unsafe-state signal (sub-mode).  Safe sub-modes (Apr-23 build):
        //   0x0D = gameplay variant (observed live while mod-opened panel is active)
        //   0x0F = hud-info + hud-play + quickslot                       (gameplay, no interaction)
        //   0x10 = hud-info + hud-play + interaction + quickslot         (gameplay, interaction in range)
        // 0x0E between them is "ingamemenu" (pre-Apr-23 it was normal gameplay) — MUST NOT open.
        // Whitelist explicitly — a threshold check would wrongly accept 0x0E.
        uintptr_t mc = (uintptr_t)InterlockedCompareExchange64(&g_mainChar, 0, 0);
        bool inSafeState = true;
        if (mc && !InterlockedCompareExchange(&g_warehouseActive, 0, 0)) {
            uint8_t curSub = ((uint8_t*)mc)[g_offSubByte];
            inSafeState = (curSub == 0x0D || curSub == 0x0F || curSub == 0x10);
        }

        if (!inSafeState) continue;

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

        // Per-panel hotkeys. Each panel has an optional VK code in
        // g_panels[i].hotkey. Behavior:
        //   - Warehouse closed → open panel i
        //   - Warehouse open → close (regardless of which panel was active)
        // No in-place panel switching — the game's UI doesn't refresh items
        // when handler+0x170 is rebound to a different container without the
        // 0xC2 context-bind command. Users close one chest and reopen the
        // next one for a clean fresh-open every time.
        static bool panelDown[PANEL_COUNT] = {};
        for (int i = 0; i < PANEL_COUNT; i++) {
            if (!g_panels[i].hotkey) { panelDown[i] = false; continue; }
            bool d = (GetAsyncKeyState(g_panels[i].hotkey) & 0x8000) != 0;
            bool modOk = (g_panels[i].modifier == 0) ||
                         (GetAsyncKeyState(g_panels[i].modifier) & 0x8000) != 0;
            if (d && modOk && !panelDown[i]) {
                panelDown[i] = true;
                DWORD now = GetTickCount();
                if (now - g_lastAct < 400) continue;
                g_lastAct = now;

                if (!InterlockedCompareExchange(&g_warehouseActive, 0, 0)) {
                    // Cold open with target panel
                    InterlockedExchange(&g_nextOpenPanel, i);
                }
                PostMessageA(g_gameWindow, WM_TRIGGER_WAREHOUSE, 1, 0);
            } else if (!d) {
                panelDown[i] = false;
            }
        }

        // Controller: B button always closes warehouse, plus per-panel buttons
        // open their respective panel from cold (or close if open).
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
                } else {
                    // Per-panel controller buttons. Each panel's button is a
                    // toggle: opens that panel from cold, or closes the
                    // warehouse if any panel is currently open.
                    for (int i = 0; i < PANEL_COUNT; i++) {
                        WORD btn = g_panels[i].controllerButton;
                        if (!btn || !(pressed & btn)) continue;
                        WORD mod = g_panels[i].controllerModifier;
                        if (mod && !(buttons & mod)) continue;

                        DWORD now = GetTickCount();
                        if (now - g_lastAct < 400) continue;
                        g_lastAct = now;

                        if (!InterlockedCompareExchange(&g_warehouseActive, 0, 0)) {
                            InterlockedExchange(&g_nextOpenPanel, i);
                        }
                        trigger = true;
                        break;
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

    // Resolve HideSubCtrl (FUN_140b99b40) — symmetric "hide" counterpart to the
    // "show" function FUN_140b999c0 that the game calls in SetDonationFaction's
    // success path. Used to hide the donation sub-controller for Private Storage
    // (no NPC context), making the Apr-23-default-visible factiondonation keyguide
    // disappear. Identified by its first instruction `MOV byte [RCX+0xB5], 0`
    // (bytes C6 81 B5 00 00 00 00) — unique in the binary (verified Apr-23 build).
    {
        static const uint8_t pHideMov[] = {
            0xC6, 0x81, 0xB5, 0x00, 0x00, 0x00, 0x00
        };
        uintptr_t match = ScanPattern(pHideMov, sizeof(pHideMov));
        if (match) {
            g_fnHideSubCtrl = FindFunctionStart(match);
        }
        Log("HideSubCtrl:  %s base+0x%llX (MOV [rcx+0xB5],0 pattern)",
            g_fnHideSubCtrl ? "OK" : "FAIL",
            g_fnHideSubCtrl ? (unsigned long long)(g_fnHideSubCtrl - g_gameBase) : 0);
    }

    // Step 3d: Extract 0x15 "prepare" sub-object offsets directly from the Handler body.
    // The Handler's 0x15 path does three back-to-back virtual calls of the form:
    //     MOV RCX, [param_1+disp32]   ; REX 8B ModRM(mod=10, reg=001 RCX, r/m != SIB) disp32
    //     MOV RAX, [RCX]              ; 48 8B 01
    //     CALL [RAX+imm]              ; FF 50 disp8  OR  FF 90 disp32
    // Apr-11 layout: 0x2c8/0x2d8/0x300.  Apr-23 layout: 0x2e8/0x2f8/0x320.
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

    // Step 4b: Modal dialog offset (update-proof modal detection)
    // Observed live (Apr-23 build, user-confirmed via field dump): the current-modal
    // pointer lives at handler + 0x258 — NOT in the 0x300-0x400 sub-controller slot
    // range where earlier builds kept it. All previous scan heuristics (store-pattern,
    // load-pattern, LEA-out-param) found false positives in 0x3XX because there are
    // unrelated struct fields there that match similar byte patterns. 0x258 sits in a
    // different part of the struct that the heuristics can't reach without producing
    // many false hits. Until we have a uniquely-identifying pattern, hardcode.
    g_modalDialogOff = 0x258;
    Log("ModalDlgOff:  OK offset=0x%X (hardcoded for Apr-23 1.0.4.1)", g_modalDialogOff);

    // Step 5a: Find mainChar singleton global
    // Pattern: MOV RAX,[RIP+disp32]; MOV RCX,[RAX+0x48]; CMP byte [RCX+0xCA8], imm8
    // The 10-byte tail "48 8B 48 48 80 B9 A8 0C 00 00" is preceded by "48 8B 05 disp32"
    {
        static const uint8_t tailPat[] = {0x48,0x8B,0x48,0x48, 0x80,0xB9,0xA8,0x0C,0x00,0x00};
        uint8_t* base = (uint8_t*)g_gameBase;
        for (DWORD i = 7; i + sizeof(tailPat) < g_imageSize; i++) {
            if (memcmp(base + i, tailPat, sizeof(tailPat)) != 0) continue;
            // Check the 7 bytes before: must be MOV RAX, [RIP+disp32] (48 8B 05 xx xx xx xx)
            uint8_t* pre = base + i - 7;
            if (pre[0] == 0x48 && pre[1] == 0x8B && (pre[2] & 0xC7) == 0x05) {
                int32_t disp = *(int32_t*)(pre + 3);
                g_mainCharGlobalPtr = (uintptr_t)(base + i) + disp; // RIP at end of MOV = base+i
                Log("MainCharGlobal: OK base+0x%llX (singleton scan)",
                    (unsigned long long)(g_mainCharGlobalPtr - g_gameBase));
                break;
            }
        }
        if (!g_mainCharGlobalPtr) Log("MainCharGlobal: FAIL (singleton pattern not found)");
    }

    // Step 5b: ModeSwitcher — string-xref + dynamic offset extraction
    // The ModeSwitcher function references 4 mainChar offsets in the 0x0C00-0x0D00 range:
    //   mode byte (u8), sub byte (u8), mode flags array (7 bytes), subtypes array (16 bytes)
    // Find any disp32 in that range — take min and max, derive the other offsets.

    // Helper lambda: scan function body for disp32 values in mainChar mode-byte range.
    // Strategy: collect all disp32 in 0xC00-0xD00, find the consecutive pair (X, X+1)
    // which identifies mode byte + sub byte. Then find the max disp for subtypes/flags.
    // Returns true and populates g_fnModeSwitcher + offsets on success.
    auto tryValidateModeSwitcher = [](uintptr_t candidate, int scanWindow, const char* method) -> bool {
        uint8_t* fn = (uint8_t*)candidate;
        // Collect all unique disp32 values in range
        uint32_t found[64];
        int nFound = 0;
        for (int k = 2; k < scanWindow - 4; k++) {
            uint8_t modrmA = fn[k - 1];
            uint8_t modrmB = fn[k - 2];
            bool caseA = ((modrmA & 0xC0) == 0x80) && ((modrmA & 0x07) != 0x04);
            bool caseB = ((modrmB & 0xC0) == 0x80) && ((modrmB & 0x07) == 0x04);
            if (!caseA && !caseB) continue;
            uint32_t disp = *(uint32_t*)(fn + k);
            if (disp < 0xC00 || disp >= 0xD00) continue;
            // Add if not already seen
            bool dup = false;
            for (int j = 0; j < nFound; j++) if (found[j] == disp) { dup = true; break; }
            if (!dup && nFound < 64) found[nFound++] = disp;
        }
        // Find the consecutive pair (X, X+1) — this is mode byte + sub byte
        uint32_t modeByte = 0;
        for (int i = 0; i < nFound; i++) {
            for (int j = 0; j < nFound; j++) {
                if (found[j] == found[i] + 1) { modeByte = found[i]; break; }
            }
            if (modeByte) break;
        }
        if (!modeByte) return false;
        // Find the max disp within modeByte+0x20 range (mode/sub/flags/subtypes are
        // clustered within ~0x20 bytes of each other in the mainChar struct)
        uint32_t maxDisp = 0;
        for (int i = 0; i < nFound; i++) {
            if (found[i] > modeByte + 1 && found[i] <= modeByte + 0x20 && found[i] > maxDisp)
                maxDisp = found[i];
        }
        // Need at least mode, sub, and one more offset for flags/subtypes
        if (!maxDisp) return false;
        g_fnModeSwitcher = candidate;
        g_offModeByte  = modeByte;
        g_offSubByte   = modeByte + 1;
        g_offSubtypes  = maxDisp;
        g_offModeFlags = maxDisp - 7;
        Log("ModeSwitcher: OK base+0x%llX (mode=0x%X sub=0x%X flags=0x%X subtypes=0x%X) [%s]",
            (unsigned long long)(candidate - g_gameBase),
            g_offModeByte, g_offSubByte, g_offModeFlags, g_offSubtypes, method);
        return true;
    };

    // PRIMARY: String-xref via "ingame-global" (unique string, update-resistant)
    {
        uintptr_t strIG = FindString("ingame-global");
        if (strIG) {
            uintptr_t leaAddr = FindLEA(strIG);
            if (leaAddr) {
                uintptr_t fnStart = FindFunctionStart(leaAddr);
                if (fnStart) {
                    tryValidateModeSwitcher(fnStart, 0xA00, "string-xref");
                }
            }
        }
    }

    // FALLBACK: Pattern scan with old + new prologs, extended scan window
    if (!g_fnModeSwitcher) {
        static const uint8_t pMS_old[] = {
            0x48,0x89,0x5C,0x24,0x08, 0x48,0x89,0x6C,0x24,0x10,
            0x48,0x89,0x74,0x24,0x18, 0x57, 0x48,0x81,0xEC,0xA0,0x00,0x00,0x00
        };
        static const uint8_t pMS_new[] = {
            0x48,0x89,0x5C,0x24,0x08, 0x48,0x89,0x74,0x24,0x18,
            0x55, 0x57, 0x41,0x56, 0x48,0x8B,0xEC
        };
        struct { const uint8_t* pat; int len; const char* tag; } patterns[] = {
            { pMS_new, sizeof(pMS_new), "pattern-new" },
            { pMS_old, sizeof(pMS_old), "pattern-old" },
        };
        uint8_t* base = (uint8_t*)g_gameBase;
        for (auto& p : patterns) {
            if (g_fnModeSwitcher) break;
            for (DWORD i = 0; (DWORD)(i + p.len) <= g_imageSize; i++) {
                if (memcmp(base + i, p.pat, p.len) != 0) continue;
                if (tryValidateModeSwitcher(g_gameBase + i, 0xA00, p.tag))
                    break;
            }
        }
    }
    if (!g_fnModeSwitcher) Log("ModeSwitcher: FAIL (no validated match)");

    // Step 6: SetCursorVisible — removed.
    // The ModeSwitcher function (FUN_1406CE4A0) is a pure mode-string configurator
    // with no cursor-related callees.  The game handles cursor visibility natively
    // when entering/leaving storage mode via the mode byte system.
    g_fnSetCursorVisible = 0;

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

    // Type-name resolver — hardcoded for CD 1.0.4.2.
    // - 0x5E8F768: slot holding the canonical "Housing_GatheredMaterials" string pointer
    //   (set by the namespace setup function FUN_140168a10 via FUN_1402ffe80(...))
    // - 0xEE1ECD0: function (char* name, short* outId) → returns 1 + writes id to outId
    g_pHGMStringSlot    = g_gameBase + 0x5E8F768;
    g_fnTypeNameLookup  = g_gameBase + 0xEE1ECD0;
    Log("HGM string slot: base+0x%llX", (unsigned long long)(g_pHGMStringSlot   - g_gameBase));
    Log("Type resolver:   base+0x%llX", (unsigned long long)(g_fnTypeNameLookup - g_gameBase));

    // === Weg G diagnostics: container singleton-factory addresses ===
    // Hardcoded RVAs from 1.0.4.2 RE. Validate at startup by reading the
    // first few bytes — if they don't look like a vtable / valid prolog,
    // skip and log a warning so the user can update the offsets after a patch.
    g_addrContainerVtable     = g_gameBase + 0x4A7D610;
    g_addrFactorySingletonVt  = g_gameBase + 0x4A5BE00;
    g_addrSingletonTypeIdSlot = g_gameBase + 0x5E3D654;
    g_addrSingletonGetter     = g_gameBase + 0xA7CDFB0;
    g_addrFactoryWrapper      = g_gameBase + 0xA9EDC10;
    g_addrInventoryInfoMgrPtr = g_gameBase + 0x5F0DA18;
    Log("Container vtable:    base+0x%llX", (unsigned long long)(g_addrContainerVtable    - g_gameBase));
    Log("Factory singleton vt: base+0x%llX", (unsigned long long)(g_addrFactorySingletonVt - g_gameBase));
    Log("Singleton type-ID:   base+0x%llX (= 0x%08X)",
        (unsigned long long)(g_addrSingletonTypeIdSlot - g_gameBase),
        *(uint32_t*)g_addrSingletonTypeIdSlot);
    Log("Singleton getter:    base+0x%llX", (unsigned long long)(g_addrSingletonGetter - g_gameBase));
    Log("Factory wrapper:     base+0x%llX", (unsigned long long)(g_addrFactoryWrapper  - g_gameBase));
    Log("Inventory mgr ptr:   base+0x%llX", (unsigned long long)(g_addrInventoryInfoMgrPtr - g_gameBase));

    return g_fnHandler && g_fnModeSwitcher && g_fnCanShow && g_fnSetInventory && g_mainCharGlobalPtr;
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

    Log("=== Private Storage Anywhere v1.4.1 ===");
    {char cls[256]={};char ttl[256]={};GetClassNameA(g_gameWindow,cls,256);GetWindowTextA(g_gameWindow,ttl,256);
    Log("Game window: class='%s' title='%s'",cls,ttl);}
    g_gameBase=(uintptr_t)GetModuleHandleA("CrimsonDesert.exe");
    if(!g_gameBase){Log("FATAL: no game base");return 0;}
    MODULEINFO mi;GetModuleInformation(GetCurrentProcess(),(HMODULE)g_gameBase,&mi,sizeof(mi));
    g_imageSize=mi.SizeOfImage;
    Log("Base: 0x%llX  Size: 0x%X  Hotkey: 0x%02X",
        (unsigned long long)g_gameBase, g_imageSize, g_hotkey);

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

    // Compute hook sizes (find clean instruction boundaries)
    g_hookSizeHandler = FindPrologBoundary((uint8_t*)g_fnHandler, 14);
    if (g_hookSizeHandler < 14) g_hookSizeHandler = 15;   // fallback

    // Save original bytes before hooking (for cleanup on unload)
    memcpy(g_origHandlerBytes, (void*)g_fnHandler, g_hookSizeHandler);
    g_hookAddrHandler = g_fnHandler;
    memcpy(g_origCanShowBytes, (void*)g_fnCanShow, 14);
    g_hookAddrCanShow = g_fnCanShow;

    if(!InstallHook(g_fnHandler,(uintptr_t)&CaptureOnHandler,"Handler",g_hookSizeHandler)) return 0;
    // ModeSwitcher hook removed: mainChar is now resolved via singleton global,
    // and the dispatcher function has a different signature (4 args, not 1).
    if(!InstallCanShowHook(g_fnCanShow)) return 0;

    // Hook the housing-storage container factory. When the game calls it
    // (player approaches chest, panel-load triggers, etc.), CaptureOnFactory
    // records the singleton + controller args. We use those in the F7 path
    // to feed the factory ourselves — same args as the game uses, no fakes.
    if (g_addrFactoryWrapper) {
        if (!InstallHook(g_addrFactoryWrapper, (uintptr_t)&CaptureOnFactory,
                         "Factory")) {
            Log("Factory hook FAILED — F7 will fall back to fake-owner path");
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

    // Dedicated worker for the InventoryInfo slot patch. Walks the
    // InventoryInfoManager singleton (resolved via Ghidra: base+0x5F0DA18)
    // and rewrites every InventoryInfo+0x48 with value 10 to 1000 — this
    // is the *real* slot-count field consumed by the UI. Manager loads
    // some time after the binary maps; poll once per second until we see
    // a non-zero patch count, then keep checking every 30s in case a
    // save-load reset reverts the values.
    CreateThread(nullptr, 0, [](LPVOID) -> DWORD {
        bool firstApplied = false;
        for (;;) {
            int n = PatchInventoryInfoSlots();
            if (n > 0) {
                if (!firstApplied) {
                    Log("InventoryInfo slot patch: %d entries default 10 -> 1000", n);
                    firstApplied = true;
                    InterlockedExchange(&g_inventorySlotPatchApplied, 1);
                } else {
                    Log("InventoryInfo slot patch: re-applied to %d entries (post-reload)", n);
                }
            }
            Sleep(firstApplied ? 30000 : 1000);
        }
        return 0;
    }, nullptr, 0, nullptr);

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
            VirtualProtect((void*)g_hookAddrHandler, g_hookSizeHandler, PAGE_EXECUTE_READWRITE, &op);
            memcpy((void*)g_hookAddrHandler, g_origHandlerBytes, g_hookSizeHandler);
            VirtualProtect((void*)g_hookAddrHandler, g_hookSizeHandler, op, &op);
            FlushInstructionCache(GetCurrentProcess(), (void*)g_hookAddrHandler, g_hookSizeHandler);
        }
        // ModeSwitcher hook removed (mainChar via singleton, no hook needed)
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
