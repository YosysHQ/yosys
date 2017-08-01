#
#   yosys -- Yosys Open SYnthesis Suite
#
#   Copyright (C) 2017  Sebastian Wallat <sebastian.wallat@rub.de>
#
#   Permission to use, copy, modify, and/or distribute this software for any
#   purpose with or without fee is hereby granted, provided that the above
#   copyright notice and this permission notice appear in all copies.
#
#   THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
#   WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
#   MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
#   ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
#   WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
#   ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
#   OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
#  
#  
#   ToDo: implement and test verific and emscripten support
#   ToDo: Fix tests to support out of source builds and unit-tests

cmake_minimum_required(VERSION 3.9)

#compiler options
option(BUILD_MINGW "BUILD_MINGW" OFF)
option(BUILD_MYSYS "BUILD_MYSYS" OFF)
option(BUILD_CLANG "BUILD_CLANG" OFF)
option(BUILD_GCC "BUILD_GCC" OFF)
option(BUILD_GCC-4.8 "BUILD_GCC-4.8" OFF)
option(BUILD_EMSCRIPTEN "BUILD_EMSCRIPTEN" OFF)

#Set compiler
if(BUILD_MINGW)
    set(CMAKE_CXX_COMPILER /usr/local/src/mxe/usr/bin/i686-w64-mingw32.static-gcc)
    set(CMAKE_CXX_LINK_EXECUTABLE /usr/local/src/mxe/usr/bin/i686-w64-mingw32.static-gcc)
elseif(BUILD_MYSYS)
    find_program(mingw-gcc i686-w64-mingw32-gcc)
    set(CMAKE_CXX_COMPILER ${mingw-gcc})
    set(CMAKE_CXX_LINK_EXECUTABLE ${mingw-gcc})
elseif(BUILD_CLANG)
    find_program(clang-exec clang)
    find_program(clang++-exec clang++)
    set(CMAKE_CXX_COMPILER ${clang-exec})
    set(CMAKE_CXX_LINK_EXECUTABLE ${clang++-exec})
elseif(BUILD_GCC)
    find_program(gcc-exec gcc)
    set(CMAKE_CXX_COMPILER ${gcc-exec})
    set(CMAKE_CXX_LINK_EXECUTABLE ${gcc-exec})
elseif(BUILD_GCC-4.8)
    find_program(gcc-4.8-exec gcc-4.8)
    set(CMAKE_CXX_COMPILER ${gcc-4.8-exec})
    set(CMAKE_CXX_LINK_EXECUTABLE ${gcc-4.8-exec})
endif()

# Configure CCache if available
find_program(CCACHE_FOUND ccache)
if(CCACHE_FOUND)
    set_property(GLOBAL PROPERTY RULE_LAUNCH_COMPILE ${CCACHE_FOUND})
    set_property(GLOBAL PROPERTY RULE_LAUNCH_LINK ${CCACHE_FOUND})
    message(STATUS "ccache found!")
endif(CCACHE_FOUND)

project(yosys)

#Add path to CMake script files
set(CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/cmake/" "${CMAKE_SOURCE_DIR}/cmake/sanitizers" "${CMAKE_MODULE_PATH}")

# features (the more the better)
option(ENABLE_TCL "ENABLE_TCL" ON)
option(ENABLE_ABC "ENABLE_ABC" ON)
option(ENABLE_PLUGINS "ENABLE_PLUGINS" ON)
option(ENABLE_READLINE "ENABLE_READLINE" ON)
option(ENABLE_VERIFIC "ENABLE_VERIFIC" OFF)
option(ENABLE_COVER "ENABLE_COVER" ON)
option(ENABLE_LIBYOSYS "ENABLE_LIBYOSYS" ON)

# other configuration flags
option(ENABLE_GPROF "ENABLE_GPROF" OFF)
option(ENABLE_NDEBUG "ENABLE_NDEBUG" OFF)
option(ENABLE_COVER "ENABLE_COVER" OFF)
option(LINK_CURSES "LINK_CURSES" ON)
option(LINK_TERMCAP "LINK_TERMCAP" OFF)
option(SMALL "SMALL" OFF)
option(ENABLE_TESTS "ENABLE_TESTS" ON)

# clang sanitizers
option(ENABLE_ADDERSS_SANITIZER "ENABLE_ADDERSS_SANITIZER" OFF)
option(ENABLE_MEMORY_SANITIZER "ENABLE_MEMORY_SANITIZER" OFF)
option(ENABLE_UNDEFINED_SANITIZER "ENABLE_UNDEFINED_SANITIZER" OFF)
option(ENABLE_CFI_SANITIZER "ENABLE_CFI_SANITIZER" OFF)


set(CMAKE_INSTALL_PREFIX "/usr/local")
include(GNUInstallDirs)
message(STATUS "CMAKE_INSTALL_BINDIR: ${CMAKE_INSTALL_BINDIR}")
message(STATUS "CMAKE_INSTALL_FULL_BINDIR: ${CMAKE_INSTALL_FULL_BINDIR}")
message(STATUS "CMAKE_INSTALL_LIBDIR: ${CMAKE_INSTALL_LIBDIR}")
message(STATUS "CMAKE_INSTALL_FULL_LIBDIR: ${CMAKE_INSTALL_FULL_LIBDIR}")
set(CMAKE_INSTALL_DATADIR ${CMAKE_INSTALL_DATADIR}/yosys)
set(CMAKE_INSTALL_FULL_DATADIR ${CMAKE_INSTALL_FULL_DATADIR}/yosys)
message(STATUS "CMAKE_INSTALL_DATADIR: ${CMAKE_INSTALL_DATADIR}")
message(STATUS "CMAKE_INSTALL_FULL_DATADIR: ${CMAKE_INSTALL_FULL_DATADIR}")
set(YOSYS_INCLUDE_DATADIR ${CMAKE_INSTALL_DATADIR}/include)
set(YOSYS_INCLUDE_FULL_DATADIR ${CMAKE_INSTALL_FULL_DATADIR}/include)
message(STATUS "YOSYS_INCLUDE_DATADIR: ${YOSYS_INCLUDE_DATADIR}")
message(STATUS "YOSYS_INCLUDE_FULL_DATADIR: ${YOSYS_INCLUDE_FULL_DATADIR}")

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra -MD ")

if(ENABLE_NDEBUG)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O3 -DNDEBUG")
else(NOT ENABLE_NDEBUG)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Os")
endif(ENABLE_NDEBUG)

if(APPLE)
    find_program(homebrew brew)
    find_program(macports port)
    if(NOT homebrew STREQUAL "homebrew-NOTFOUND")
        # homebrew search paths
        execute_process(COMMAND brew --prefix OUTPUT_VARIABLE BREW_PREFIX)
        string(STRIP ${BREW_PREFIX} BREW_PREFIX)
        set(BREW_PREFIX ${BREW_PREFIX}/opt)
        set(ENV{PKG_CONFIG_PATH} "${BREW_PREFIX}/libffi/lib/pkgconfig:${BREW_PREFIX}/tcl-tk/lib/pkgconfig:$ENV{PKG_CONFIG_PATH}")
        set(ENV{PATH} "${BREW_PREFIX}/flex/bin:${BREW_PREFIX}/bison/bin:${BREW_PREFIX}/gettext/bin:$ENV{PATH}")
        set(Readline_ROOT_DIR "${BREW_PREFIX}/readline/")
    elseif(NOT macports STREQUAL "macports-NOTFOUND")
        # macports search paths
        set(PORT_PREFIX ${macports})
        string(REPLACE /bin/port "" PORT_PREFIX ${PORT_PREFIX})
        set(ENV{PKG_CONFIG_PATH} "${PORT_PREFIX}/lib/pkgconfig:$ENV{PKG_CONFIG_PATH}")
        set(ENV{PATH} "${PORT_PREFIX}/bin:$ENV{PATH}")
        include_directories(${PORT_PREFIX}/include)
        link_directories(${PORT_PREFIX}/lib)
    endif(NOT homebrew STREQUAL "homebrew-NOTFOUND")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fPIC")
endif(APPLE)

if(CMAKE_CXX_COMPILER_ID MATCHES "Clang" OR "${CMAKE_CXX_COMPILER_ID}" STREQUAL "GNU")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fPIC -ggdb")
elseif(MINGW)
    set(ENV{PKG_CONFIG} /usr/local/src/mxe/usr/bin/i686-w64-mingw32.static-pkg-config)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D_POSIX_SOURCE -DYOSYS_MXE_HACKS -Wno-attributes -ggdb")
    set(ABCMKARGS "ARCHFLAGS=\"-DSIZEOF_VOID_P=4 -DSIZEOF_LONG=4 -DSIZEOF_INT=4 -DWIN32_NO_DLL -DHAVE_STRUCT_TIMESPEC -fpermissive -w\"")
    set(ABCMKARGS "${ABCMKARGS} LIBS=\"lib/x86/pthreadVC2.lib -s\" ABC_USE_NO_READLINE=1")
elseif(MYSYS)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -D_POSIX_SOURCE -DYOSYS_WIN32_UNIX_DIR -ggdb")
    set(ABCMKARGS "ARCHFLAGS=\"-DSIZEOF_VOID_P=4 -DSIZEOF_LONG=4 -DSIZEOF_INT=4 -DWIN32_NO_DLL -DHAVE_STRUCT_TIMESPEC -fpermissive -w\"")
    set(ABCMKARGS "${ABCMKARGS} LIBS=\"lib/x86/pthreadVC2.lib -s\" ABC_USE_NO_READLINE=0")
endif()

find_package(PkgConfig REQUIRED)
find_package(Bison REQUIRED)
find_package(Flex REQUIRED)
find_package(Gettext REQUIRED)
set(Python_ADDITIONAL_VERSIONS 3.5 3.6)
find_package(PythonInterp 3.6 REQUIRED)
if(ENABLE_PLUGINS)
    find_package(LibFFI REQUIRED)
endif(ENABLE_PLUGINS)
if(ENABLE_READLINE)
    find_package(Readline REQUIRED)
    if(LINK_CURSES)
        find_package(Curses REQUIRED)
        set(ABCMKARGS "${ABCMKARGS} ABC_READLINE_LIBRARIES=-lcurses -lreadline")
    endif(LINK_CURSES)
    if(LINK_TERMCAP)
        find_package(Termcap REQUIRED)
        set(ABCMKARGS "${ABCMKARGS} ABC_READLINE_LIBRARIES=-lreadline -ltermcap")
    endif(LINK_TERMCAP)
endif(ENABLE_READLINE)
if(ENABLE_TCL)
    find_package(TCL REQUIRED)
endif(ENABLE_TCL)
find_package(Sanitizers)

set(YOSYS_SRC ${CMAKE_CURRENT_BINARY_DIR})
set(DATDIR ${CMAKE_INSTALL_DATADIR})
execute_process(COMMAND test -e .git COMMAND git log --author=clifford@clifford.at --oneline 61f6811.. COMMAND wc -l OUTPUT_VARIABLE YOSYS_VER_TMP)
string(STRIP ${YOSYS_VER_TMP} YOSYS_VER_TMP)
set(YOSYS_VER 0.7+${YOSYS_VER_TMP})

execute_process(COMMAND git rev-parse --short HEAD OUTPUT_VARIABLE GIT_REV)
string(STRIP ${GIT_REV} GIT_REV)
if(GIT_REV STREQUAL "")
    set(GIT_REV "UNKNOWN")
endif()

set(YOSYS_VER_STR "Yosys ${YOSYS_VER} (git sha1 ${GIT_REV}, ${CMAKE_CXX_COMPILER_ID} ${CMAKE_CXX_COMPILER_VERSION}, ${CMAKE_CXX_FLAGS})")
message(STATUS YOSYS_VER_STR="${YOSYS_VER_STR}")
configure_file("kernel/version.cc.in" "${CMAKE_CURRENT_BINARY_DIR}/kernel/version_${GIT_REV}.cc" @ONLY)

if(ENABLE_ABC)
    # set 'ABCREV = default' to use abc/ as it is
    #
    # Note: If you do ABC development, make sure that 'abc' in this directory
    # is just a symlink to your actual ABC working directory, as 'make mrproper'
    # will remove the 'abc' directory and you do not want to accidentally
    # delete your work on ABC..
    set(ABCREV "efbf7f13ea9e")
    set(ABCPULL "1")
    if(NOT ABCURL)
        set(ABCURL "https://bitbucket.org/alanmi/abc")
    endif(NOT ABCURL)
    set(ABCMKARGS "${ABCMKARGS} CC=\"${CMAKE_CXX_COMPILER}\" CXX=\"${CMAKE_CXX_COMPILER}\"")
    # set ABCEXTERNAL = <abc-command> to use an external ABC instance
    # Note: The in-tree ABC (yosys-abc) will not be installed when ABCEXTERNAL is set.
    #    set(ABCEXTERNAL "")
    if(NOT ABCEXTERNAL)
        include(ExternalProject)
        externalproject_add(abc
                            SOURCE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/abc
                            BUILD_IN_SOURCE 0
                            UPDATE_COMMAND ""
                            HG_REPOSITORY ${ABCURL}
                            HG_TAG ${ABCREV}
                            BUILD_COMMAND make ${ABCMKARGS}
                            BINARY_DIR ${CMAKE_CURRENT_BINARY_DIR}/abc
                            INSTALL_COMMAND cmake -E echo "Skipping install step."
                            )
        externalproject_get_property(abc install_dir)
        add_custom_target(yosys-abc
                          BYPRODUCTS yosys-abc${CMAKE_EXECUTABLE_SUFFIX}
                          COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_BINARY_DIR}/abc/abc${CMAKE_EXECUTABLE_SUFFIX} ${CMAKE_CURRENT_BINARY_DIR}/yosys-abc${CMAKE_EXECUTABLE_SUFFIX}
                          COMMENT "Copy abc executable to yosis-abc${CMAKE_EXECUTABLE_SUFFIX}"
                          )
        add_dependencies(yosys-abc abc)
        install(FILES ${CMAKE_CURRENT_BINARY_DIR}/yosys-abc${CMAKE_EXECUTABLE_SUFFIX} DESTINATION ${CMAKE_INSTALL_BINDIR} PERMISSIONS OWNER_EXECUTE OWNER_WRITE OWNER_READ
                GROUP_EXECUTE GROUP_READ WORLD_READ WORLD_EXECUTE)
    endif(NOT ABCEXTERNAL)
endif(ENABLE_ABC)

if(ENABLE_GPROF)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -pg")
endif(ENABLE_GPROF)

set(CMAKE_CXX_STANDARD 11)

include_directories(${CMAKE_CURRENT_SOURCE_DIR} ${CMAKE_CURRENT_BINARY_DIR})

set(INSTALL_HEADER_FILES
    kernel/yosys.h
    kernel/hashlib.h
    kernel/log.h
    kernel/rtlil.h
    kernel/register.h
    kernel/celltypes.h
    kernel/celledges.h
    kernel/consteval.h
    kernel/sigtools.h
    kernel/modtools.h
    kernel/macc.h
    kernel/utils.h
    kernel/satgen.h
    libs/ezsat/ezsat.h
    libs/ezsat/ezminisat.h
    libs/sha1/sha1.h
    passes/fsm/fsmdata.h
    frontends/ast/ast.h
    backends/ilang/ilang_backend.h
    )

install(FILES ${INSTALL_HEADER_FILES} DESTINATION "${YOSYS_INCLUDE_DATADIR}")

if(ENABLE_READLINE)
    include_directories(${Readline_INCLUDE_DIR})
    link_libraries(${Readline_LIBRARY})
    add_definitions(-DYOSYS_ENABLE_READLINE)
endif(ENABLE_READLINE)

if(ENABLE_TCL)
    include_directories(${TCL_INCLUDE_PATH}
                        ${TK_INCLUDE_PATH})
    link_libraries(${TCL_LIBRARY} ${TK_LIBRARY})
    add_definitions(-DYOSYS_ENABLE_TCL)
endif(ENABLE_TCL)

if(ENABLE_ABC)
    add_definitions(-DYOSYS_ENABLE_ABC)
endif(ENABLE_ABC)

if(ENABLE_PLUGINS)
    include_directories(${LIBFFI_INCLUDE_DIR})
    link_libraries(${LIBFFI_LIBRARY})
    add_definitions(-DYOSYS_ENABLE_PLUGINS)
endif(ENABLE_PLUGINS)

if(ENABLE_COVER)
    add_definitions(-DYOSYS_ENABLE_COVER)
endif(ENABLE_COVER)

if(NOT SEED)
    set(SEEDOPT "-S ${SEED}")
else()
    set(SEEDOPT "")
endif(NOT SEED)

add_definitions(-D_YOSYS_ -DYOSYS_SRC="${YOSYS_SRC}" -DYOSYS_DATADIR="${DATDIR}")

set(SOURCE_FILES
    kernel/version_${GIT_REV}.cc

    kernel/calc.cc
    kernel/cellaigs.cc
    kernel/celledges.cc
    kernel/log.cc
    kernel/register.cc
    kernel/rtlil.cc
    kernel/yosys.cc

    libs/bigint/BigInteger.cc
    libs/bigint/BigIntegerAlgorithms.cc
    libs/bigint/BigIntegerUtils.cc
    libs/bigint/BigUnsigned.cc
    libs/bigint/BigUnsignedInABase.cc

    libs/sha1/sha1.cpp
    )

include(backends/CMakeLists.txt)
include(frontends/CMakeLists.txt)
include(passes/CMakeLists.txt)
include(techlibs/CMakeLists.txt)


if(NOT SMALL)
    set(SOURCE_FILES
        ${SOURCE_FILES}

        libs/subcircuit/subcircuit.cc

        libs/ezsat/ezsat.cc
        libs/ezsat/ezminisat.cc

        libs/minisat/Options.cc
        libs/minisat/SimpSolver.cc
        libs/minisat/Solver.cc
        libs/minisat/System.cc
        )
endif(NOT SMALL)

add_executable(${PROJECT_NAME} ${SOURCE_FILES} kernel/driver.cc)
if(ENABLE_ADDERSS_SANITIZER)
    add_sanitize_address(${PROJECT_NAME})
endif(ENABLE_ADDERSS_SANITIZER)

if(ENABLE_MEMORY_SANITIZER)
    add_sanitize_memory(${PROJECT_NANE})
endif(ENABLE_MEMORY_SANITIZER)

if(ENABLE_UNDEFINED_SANITIZER)
    add_sanitize_undefined(${PROJECT_NAME})
endif(ENABLE_UNDEFINED_SANITIZER)

if(ENABLE_CFI_SANITIZER)
    add_sanitize_cfi(${PROJECT_NAME})
endif(ENABLE_CFI_SANITIZER)
install(TARGETS ${PROJECT_NAME} RUNTIME DESTINATION ${CMAKE_INSTALL_BINDIR})

if(ENABLE_LIBYOSYS)
    add_library(${PROJECT_NAME}-lib SHARED ${SOURCE_FILES})
    add_dependencies(${PROJECT_NAME}-lib ${PROJECT_NAME}) # Needed to not generate passes/techmap/techmap.inc twice
    if(ENABLE_ADDERSS_SANITIZER)
        add_sanitize_address(${PROJECT_NAME}-lib)
    endif(ENABLE_ADDERSS_SANITIZER)

    if(ENABLE_MEMORY_SANITIZER)
        add_sanitize_memory(${PROJECT_NAME}-lib)
    endif(ENABLE_MEMORY_SANITIZER)

    if(ENABLE_UNDEFINED_SANITIZER)
        add_sanitize_undefined(${PROJECT_NAME}-lib)
    endif(ENABLE_UNDEFINED_SANITIZER)

    if(ENABLE_CFI_SANITIZER)
        add_sanitize_cfi(${PROJECT_NAME}-lib)
    endif(ENABLE_CFI_SANITIZER)
    install(TARGETS ${PROJECT_NAME}-lib LIBRARY DESTINATION ${CMAKE_INSTALL_LIBDIR})
endif(ENABLE_LIBYOSYS)

#Install shared files
install(DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/share DESTINATION ${CMAKE_INSTALL_DATADIR})

#Uninstall Target
# uninstall target
configure_file(
        "${CMAKE_CURRENT_SOURCE_DIR}/cmake_uninstall.cmake.in"
        "${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake"
        IMMEDIATE @ONLY)

add_custom_target(uninstall
                  COMMAND ${CMAKE_COMMAND} -P ${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake)

if(ENABLE_TESTS)
    enable_testing()
    add_test(NAME test/simple
             COMMAND run-test.sh ${SEEDOPT}
             WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/tests/simple)

    add_test(NAME test/hana
             COMMAND run-test.sh ${SEEDOPT}
             WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/tests/hana)

    add_test(NAME test/asciworld
             COMMAND run-test.sh ${SEEDOPT}
             WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/tests/asciworld)

    add_test(NAME test/realmath
             COMMAND run-test.sh ${SEEDOPT}
             WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/tests/realmath)

    add_test(NAME test/share
             COMMAND run-test.sh ${SEEDOPT}
             WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/tests/share)

    add_test(NAME test/fsm
             COMMAND run-test.sh ${SEEDOPT}
             WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/tests/fsm)

    add_test(NAME test/techmap
             COMMAND run-test.sh ${SEEDOPT}
             WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/tests/techmap)

    add_test(NAME test/memories
             COMMAND run-test.sh ${SEEDOPT}
             WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/tests/memories)

    add_test(NAME test/bram
             COMMAND run-test.sh ${SEEDOPT}
             WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/tests/bram)

    add_test(NAME test/various
             COMMAND run-test.sh ${SEEDOPT}
             WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/tests/various)

    add_test(NAME test/sat
             COMMAND run-test.sh ${SEEDOPT}
             WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/tests/sat)

    add_test(NAME vloghtb
             COMMAND run-test.sh
             WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/tests/vloghtb)

    find_program(valgrind_exec valgrind)
    if(valgrind_exec_FOUND)
        add_custom_target(vgtest
                          COMMAND ${valgrind_exec} ${CMAKE_CURRENT_BINARY_DIR}/yosys -p 'setattr -mod -unset top\; synth' $\(ls tests/simple/*.v | grep -v repwhile.v\)
                          COMMENT "Run valgrind tests")
    endif(valgrind_exec_FOUND)
endif(ENABLE_TESTS)