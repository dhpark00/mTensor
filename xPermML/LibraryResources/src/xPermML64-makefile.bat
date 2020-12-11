@echo off
REM *** VS2019 x64 native commandline tools environment and MMA12 ***
REM OPEN "x64 Native Tools Command Prompt"

SET MMA=c:\Mathematica12
SET CompAdd=%MMA%\SystemFiles\Links\MathLink\DeveloperKit\Windows-x86-64\CompilerAdditions
SET MPREP=%CompAdd%\mprep.exe

SET CL=/nologo /c /DWIN32 /D_WINDOWS /W3 /O2 /DNDEBUG /EHsc

SET LINK=/NOLOGO /SUBSYSTEM:windows /INCREMENTAL:no /PDB:NONE kernel32.lib user32.lib gdi32.lib

SET INCLUDE=%CompAdd%;%INCLUDE%

SET LIB=%CompAdd%;%LIB%

%MPREP% xPermML.tm -o xPermML-prep.cpp

CL xPermML-prep.cpp

LINK xPermML-prep.obj ml64i4m.lib /OUT:xPermML64.mswin

DEL *.obj

DEL xPermML-prep.cpp

