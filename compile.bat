@echo off
echo === Compiling PrivateStorageEverywhere v11.0 (ImGui Overlay) ===
cl /O2 /LD /EHsc /Isrc /Isrc/imgui /Isrc/imgui/backends ^
    src\dllmain.cpp ^
    src\imgui\imgui.cpp ^
    src\imgui\imgui_draw.cpp ^
    src\imgui\imgui_tables.cpp ^
    src\imgui\imgui_widgets.cpp ^
    src\imgui\backends\imgui_impl_win32.cpp ^
    src\imgui\backends\imgui_impl_dx12.cpp ^
    user32.lib psapi.lib d3d12.lib dxgi.lib ^
    /link /DLL /OUT:PrivateStorageEverywhere.asi
if %ERRORLEVEL% == 0 (
    echo === BUILD SUCCESS ===
    del /q *.obj 2>nul
    del /q PrivateStorageEverywhere.lib 2>nul
    del /q PrivateStorageEverywhere.exp 2>nul
    copy /Y PrivateStorageEverywhere.asi "C:\Program Files (x86)\Steam\steamapps\common\Crimson Desert\bin64\PrivateStorageEverywhere.asi"
    echo === COPIED TO GAME ===
) else (
    echo === BUILD FAILED ===
)
pause
