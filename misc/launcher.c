/* This file comes from the PyPA Setuptools repository, commit 16e452a:
https://github.com/pypa/setuptools
Modifications include this comment and inline inclusion of the LICENSE text. */

/* Copyright (C) 2016 Jason R Coombs <jaraco@jaraco.com>

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the "Software"), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
of the Software, and to permit persons to whom the Software is furnished to do
so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE. */

/*  Setuptools Script Launcher for Windows

    This is a stub executable for Windows that functions somewhat like
    Effbot's "exemaker", in that it runs a script with the same name but
    a .py extension, using information from a #! line.  It differs in that
    it spawns the actual Python executable, rather than attempting to
    hook into the Python DLL.  This means that the script will run with
    sys.executable set to the Python executable, where exemaker ends up with
    sys.executable pointing to itself.  (Which means it won't work if you try
    to run another Python process using sys.executable.)

    To build/rebuild with mingw32, do this in the setuptools project directory:

       gcc -DGUI=0           -mno-cygwin -O -s -o setuptools/cli.exe launcher.c
       gcc -DGUI=1 -mwindows -mno-cygwin -O -s -o setuptools/gui.exe launcher.c

    To build for Windows RT, install both Visual Studio Express for Windows 8
    and for Windows Desktop (both freeware), create "win32" application using
    "Windows Desktop" version, create new "ARM" target via
    "Configuration Manager" menu and modify ".vcxproj" file by adding
    "<WindowsSDKDesktopARMSupport>true</WindowsSDKDesktopARMSupport>" tag
    as child of "PropertyGroup" tags that has "Debug|ARM" and "Release|ARM"
    properties.

    It links to msvcrt.dll, but this shouldn't be a problem since it doesn't
    actually run Python in the same process.  Note that using 'exec' instead
    of 'spawn' doesn't work, because on Windows this leads to the Python
    executable running in the *background*, attached to the same console
    window, meaning you get a command prompt back *before* Python even finishes
    starting.  So, we have to use spawnv() and wait for Python to exit before
    continuing.  :(
*/

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <windows.h>
#include <tchar.h>
#include <fcntl.h>
#include <unistd.h>

int child_pid=0;

int fail(const char *format, const char *data) {
    /* Print error message to stderr and return 2 */
    fprintf(stderr, format, data);
    return 2;
}

char *quoted(char *data) {
    int i, ln = strlen(data), nb;

    /* We allocate twice as much space as needed to deal with worse-case
       of having to escape everything. */
    char *result = (char *)calloc(ln*2+3, sizeof(char));
    char *presult = result;

    *presult++ = '"';
    for (nb=0, i=0; i < ln; i++)
      {
        if (data[i] == '\\')
          nb += 1;
        else if (data[i] == '"')
          {
            for (; nb > 0; nb--)
              *presult++ = '\\';
            *presult++ = '\\';
          }
        else
          nb = 0;
        *presult++ = data[i];
      }

    for (; nb > 0; nb--)        /* Deal w trailing slashes */
      *presult++ = '\\';

    *presult++ = '"';
    *presult++ = 0;
    return result;
}










char *loadable_exe(char *exename) {
    /* HINSTANCE hPython;  DLL handle for python executable */
    char *result;

    /* hPython = LoadLibraryEx(exename, NULL, LOAD_WITH_ALTERED_SEARCH_PATH);
    if (!hPython) return NULL; */

    /* Return the absolute filename for spawnv */
    result = (char *)calloc(MAX_PATH, sizeof(char));
    strncpy(result, exename, MAX_PATH);
    /*if (result) GetModuleFileNameA(hPython, result, MAX_PATH);

    FreeLibrary(hPython); */
    return result;
}


char *find_exe(char *exename, char *script) {
    char drive[_MAX_DRIVE], dir[_MAX_DIR], fname[_MAX_FNAME], ext[_MAX_EXT];
    char path[_MAX_PATH], c, *result;

    /* convert slashes to backslashes for uniform search below */
    result = exename;
    while (c = *result++) if (c=='/') result[-1] = '\\';

    _splitpath(exename, drive, dir, fname, ext);
    if (drive[0] || dir[0]=='\\') {
        return loadable_exe(exename);   /* absolute path, use directly */
    }
    /* Use the script's parent directory, which should be the Python home
       (This should only be used for bdist_wininst-installed scripts, because
        easy_install-ed scripts use the absolute path to python[w].exe
    */
    _splitpath(script, drive, dir, fname, ext);
    result = dir + strlen(dir) -1;
    if (*result == '\\') result--;
    while (*result != '\\' && result>=dir) *result-- = 0;
    _makepath(path, drive, dir, exename, NULL);
    return loadable_exe(path);
}


char **parse_argv(char *cmdline, int *argc)
{
    /* Parse a command line in-place using MS C rules */

    char **result = (char **)calloc(strlen(cmdline), sizeof(char *));
    char *output = cmdline;
    char c;
    int nb = 0;
    int iq = 0;
    *argc = 0;

    result[0] = output;
    while (isspace(*cmdline)) cmdline++;   /* skip leading spaces */

    do {
        c = *cmdline++;
        if (!c || (isspace(c) && !iq)) {
            while (nb) {*output++ = '\\'; nb--; }
            *output++ = 0;
            result[++*argc] = output;
            if (!c) return result;
            while (isspace(*cmdline)) cmdline++;  /* skip leading spaces */
            if (!*cmdline) return result;  /* avoid empty arg if trailing ws */
            continue;
        }
        if (c == '\\')
            ++nb;   /* count \'s */
        else {
            if (c == '"') {
                if (!(nb & 1)) { iq = !iq; c = 0; }  /* skip " unless odd # of \ */
                nb = nb >> 1;   /* cut \'s in half */
            }
            while (nb) {*output++ = '\\'; nb--; }
            if (c) *output++ = c;
        }
    } while (1);
}

void pass_control_to_child(DWORD control_type) {
    /*
     * distribute-issue207
     * passes the control event to child process (Python)
     */
    if (!child_pid) {
        return;
    }
    GenerateConsoleCtrlEvent(child_pid,0);
}

BOOL control_handler(DWORD control_type) {
    /*
     * distribute-issue207
     * control event handler callback function
     */
    switch (control_type) {
        case CTRL_C_EVENT:
            pass_control_to_child(0);
            break;
    }
    return TRUE;
}

int create_and_wait_for_subprocess(char* command) {
    /*
     * distribute-issue207
     * launches child process (Python)
     */
    DWORD return_value = 0;
    LPSTR commandline = command;
    STARTUPINFOA s_info;
    PROCESS_INFORMATION p_info;
    ZeroMemory(&p_info, sizeof(p_info));
    ZeroMemory(&s_info, sizeof(s_info));
    s_info.cb = sizeof(STARTUPINFO);
    // set-up control handler callback funciotn
    SetConsoleCtrlHandler((PHANDLER_ROUTINE) control_handler, TRUE);
    if (!CreateProcessA(NULL, commandline, NULL, NULL, TRUE, 0, NULL, NULL, &s_info, &p_info)) {
        fprintf(stderr, "failed to create process.\n");
        return 0;
    }
    child_pid = p_info.dwProcessId;
    // wait for Python to exit
    WaitForSingleObject(p_info.hProcess, INFINITE);
    if (!GetExitCodeProcess(p_info.hProcess, &return_value)) {
        fprintf(stderr, "failed to get exit code from process.\n");
        return 0;
    }
    return return_value;
}

char* join_executable_and_args(char *executable, char **args, int argc)
{
    /*
     * distribute-issue207
     * CreateProcess needs a long string of the executable and command-line arguments,
     * so we need to convert it from the args that was built
     */
    int len,counter;
    char* cmdline;

    len=strlen(executable)+2;
    for (counter=1; counter<argc; counter++) {
        len+=strlen(args[counter])+1;
    }

    cmdline = (char*)calloc(len, sizeof(char));
    sprintf(cmdline, "%s", executable);
    len=strlen(executable);
    for (counter=1; counter<argc; counter++) {
        sprintf(cmdline+len, " %s", args[counter]);
        len+=strlen(args[counter])+1;
    }
    return cmdline;
}

int run(int argc, char **argv, int is_gui) {

    char python[256];   /* python executable's filename*/
    char *pyopt;        /* Python option */
    char script[256];   /* the script's filename */

    int scriptf;        /* file descriptor for script file */

    char **newargs, **newargsp, **parsedargs; /* argument array for exec */
    char *ptr, *end;    /* working pointers for string manipulation */
    char *cmdline;
    int i, parsedargc;              /* loop counter */

    /* compute script name from our .exe name*/
    GetModuleFileNameA(NULL, script, sizeof(script));
    end = script + strlen(script);
    while( end>script && *end != '.')
        *end-- = '\0';
    *end-- = '\0';
    strcat(script, (GUI ? "-script.pyw" : "-script.py"));

    /* figure out the target python executable */

    scriptf = open(script, O_RDONLY);
    if (scriptf == -1) {
        return fail("Cannot open %s\n", script);
    }
    end = python + read(scriptf, python, sizeof(python));
    close(scriptf);

    ptr = python-1;
    while(++ptr < end && *ptr && *ptr!='\n' && *ptr!='\r') {;}

    *ptr-- = '\0';

    if (strncmp(python, "#!", 2)) {
        /* default to python.exe if no #! header */
        strcpy(python, "#!python.exe");
    }

    parsedargs = parse_argv(python+2, &parsedargc);

    /* Using spawnv() can fail strangely if you e.g. find the Cygwin
       Python, so we'll make sure Windows can find and load it */

    ptr = find_exe(parsedargs[0], script);
    if (!ptr) {
        return fail("Cannot find Python executable %s\n", parsedargs[0]);
    }

    /* printf("Python executable: %s\n", ptr); */

    /* Argument array needs to be
       parsedargc + argc, plus 1 for null sentinel */

    newargs = (char **)calloc(parsedargc + argc + 1, sizeof(char *));
    newargsp = newargs;

    *newargsp++ = quoted(ptr);
    for (i = 1; i<parsedargc; i++) *newargsp++ = quoted(parsedargs[i]);

    *newargsp++ = quoted(script);
    for (i = 1; i < argc; i++)     *newargsp++ = quoted(argv[i]);

    *newargsp++ = NULL;

    /* printf("args 0: %s\nargs 1: %s\n", newargs[0], newargs[1]); */

    if (is_gui) {
        /* Use exec, we don't need to wait for the GUI to finish */
        execv(ptr, (char * const *)(newargs));
        return fail("Could not exec %s", ptr);   /* shouldn't get here! */
    }

    /*
     * distribute-issue207: using CreateProcessA instead of spawnv
     */
    cmdline = join_executable_and_args(ptr, newargs, parsedargc + argc);
    return create_and_wait_for_subprocess(cmdline);
}

int WINAPI WinMain(HINSTANCE hI, HINSTANCE hP, LPSTR lpCmd, int nShow) {
    return run(__argc, __argv, GUI);
}

int main(int argc, char** argv) {
    return run(argc, argv, GUI);
}
