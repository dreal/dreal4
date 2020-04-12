@echo off
set TARGET="Visual Studio 15 2017 Win64"
set TOOLSET=v141
set CFGS=Debug;RelWithDebInfo;Release
set OUT=VS2017_%TOOLSET%_x64
mkdir %OUT% 2>NUL
cmd /C "pushd %OUT% & cmake ../.. -G %TARGET% -T %TOOLSET% -DCMAKE_CONFIGURATION_TYPES=%CFGS%"
