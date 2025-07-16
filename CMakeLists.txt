cmake_minimum_required(VERSION 3.13)
project(yosys LANGUAGES CXX C)
set(YOSYS_VER "0.50+1")
set(CMAKE_POSITION_INDEPENDENT_CODE ON)

# features (the more the better)

option(ENABLE_TCL "Enable TCL library usage" ON)
option(ENABLE_ABC "Enable building ABC" ON)
option(LINK_ABC "Enable linking ABC as library" OFF)
option(ENABLE_GLOB "Enable usage of glob.h" ON)
option(ENABLE_PLUGINS "Enable plugins support" ON)
option(ENABLE_READLINE "Enable readline library usage" ON)
option(ENABLE_EDITLINE "Enable editline library usage" OFF)
option(ENABLE_GHDL "Enable building with GHDL plugin" OFF)
option(ENABLE_VERIFIC "Enable Verific library" OFF)
option(ENABLE_VERIFIC_SYSTEMVERILOG "Enable Verific SystemVerilog support" ON)
option(ENABLE_VERIFIC_VHDL "Enable Verific VHDL support" ON)
option(ENABLE_VERIFIC_HIER_TREE "Enable Verific hierarchy tree support" ON)
option(ENABLE_VERIFIC_YOSYSHQ_EXTENSIONS "Enable Verific YosysHQ specific extension" OFF)
option(ENABLE_VERIFIC_EDIF "Enable Verific EDIF support " OFF)
option(ENABLE_VERIFIC_LIBERTY "Enable Verific Liberty support" OFF)
option(ENABLE_COVER "Enable internal coverage" ON)
option(ENABLE_LIBYOSYS "Enable building Yosys as library" OFF)
option(ENABLE_ZLIB "Enable zlib library usage" ON)

# python wrappers
option(ENABLE_PYOSYS "Enable building Yosys Python wrapper" OFF)

# other configuration flags
option(ENABLE_GCOV "Enable gcov build" OFF)
option(ENABLE_GPROF "Enable profiler build" OFF)
option(ENABLE_DEBUG "Enable debug build" OFF)
option(ENABLE_LTO "Enable LTO build" OFF)
option(ENABLE_CCACHE "Enable building with CCACHE" OFF)
# sccache is not always a drop-in replacement for ccache in practice
option(ENABLE_SCCACHE "Enable building with SCCACHE" OFF)
option(ENABLE_FUNCTIONAL_TESTS "Enable functional tests" OFF)

# Needed for environments that can't run executables (i.e. emscripten, wasm)
option(DISABLE_SPAWN "Disable executable spawn" OFF)
# Needed for environments that don't have proper thread support (i.e. emscripten, wasm--for now)
option(DISABLE_ABC_THREADS "Disable ABC threading support" OFF)

set(CXXSTD 17 CACHE STRING "C++ standard to use for the build")


list(APPEND CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)

include(CheckCXXCompilerFlag)

if (ENABLE_ABC)
    set(ABC_USE_NAMESPACE "abc")
    add_subdirectory(abc EXCLUDE_FROM_ALL)

    add_custom_command(
        OUTPUT ${yosys_BINARY_DIR}/yosys-abc
        DEPENDS abc  # Depend on the target, not the generator expression
        COMMAND ${CMAKE_COMMAND} -E copy $<TARGET_FILE:abc> ${yosys_BINARY_DIR}/yosys-abc
    )

    add_custom_target(yosys-abc-copy ALL DEPENDS ${yosys_BINARY_DIR}/yosys-abc)
endif()

get_property(cxx_features GLOBAL PROPERTY CMAKE_CXX_KNOWN_FEATURES)
if(NOT CMAKE_CXX_STANDARD)
    if("cxx_std_20" IN_LIST cxx_features)
        message(STATUS "C++20 support enabled")
        set(CMAKE_CXX_STANDARD 20)
    elseif("cxx_std_17" IN_LIST cxx_features)
        message(STATUS "C++17 support enabled")
        set(CMAKE_CXX_STANDARD 17)
    elseif("cxx_std_14" IN_LIST cxx_features)
        message(STATUS "C++14 support enabled")
        set(CMAKE_CXX_STANDARD 14)
    elseif("cxx_std_11" IN_LIST cxx_features)
        message(STATUS "C++11 support enabled")
        set(CMAKE_CXX_STANDARD 11)
    else()
        message(STATUS "C++98 support enabled")
        set(CMAKE_CXX_STANDARD 98)
    endif()
else()
    message(STATUS "C++ standard set to ${CMAKE_CXX_STANDARD}")
endif()

set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

set(CMAKE_C_STANDARD 99)
set(CMAKE_C_STANDARD_REQUIRED ON)
set(CMAKE_C_EXTENSIONS ON)

find_package(FLEX 2.6 REQUIRED)
find_package(BISON 3.0 REQUIRED)
find_package(Python3 3.5 REQUIRED COMPONENTS Interpreter)

add_library(yosys_obj OBJECT)
include_directories(${CMAKE_CURRENT_BINARY_DIR} ${CMAKE_CURRENT_SOURCE_DIR})
target_include_directories(yosys_obj PUBLIC
    ${CMAKE_CURRENT_BINARY_DIR}
    ${CMAKE_CURRENT_SOURCE_DIR}
)

add_compile_definitions(_YOSYS_)
target_compile_definitions(yosys_obj PUBLIC _YOSYS_)

if (ENABLE_READLINE AND ENABLE_EDITLINE)
    message(FATAL_ERROR "Not possible to enable both ENABLE_READLINE and ENABLE_EDITLINE")
endif()

if (ENABLE_READLINE)
    find_package(Readline REQUIRED)
    add_compile_definitions(YOSYS_ENABLE_READLINE)
    target_link_libraries(yosys_obj PUBLIC ${READLINE_LIBRARY})
endif()

if (ENABLE_EDITLINE)
    find_package(Editline REQUIRED)
    add_compile_definitions(YOSYS_ENABLE_EDITLINE)
    target_link_libraries(yosys_obj PUBLIC ${EDITLINE_LIBRARY})
endif()

if (ENABLE_TCL)
    find_package(TCL 8.6 REQUIRED)
    add_compile_definitions(YOSYS_ENABLE_TCL)
    target_include_directories(yosys_obj PUBLIC ${TCL_INCLUDE_PATH})
    target_link_libraries(yosys_obj PUBLIC ${TCL_LIBRARY})
endif()

if (ENABLE_ZLIB)
    find_package(ZLIB REQUIRED)
    add_compile_definitions(YOSYS_ENABLE_ZLIB)
    target_link_libraries(yosys_obj PUBLIC ZLIB::ZLIB)
endif()

if (ENABLE_COVER)
    add_compile_definitions(YOSYS_ENABLE_COVER)
endif()

if (ENABLE_CCACHE)
    find_program(CCACHE_FOUND ccache)
    if (CCACHE_FOUND)
        set(CMAKE_CXX_COMPILER_LAUNCHER ccache)
        set(CMAKE_C_COMPILER_LAUNCHER ccache)
        message(STATUS "Enabling ccache")
    else()
        message(STATUS "Failed to enabling ccache")
    endif()
endif ()

if (ENABLE_SCCACHE)
    find_program(SCCACHE_FOUND sccache)
    if (SCCACHE_FOUND)
        set(CMAKE_CXX_COMPILER_LAUNCHER sccache)
        set(CMAKE_C_COMPILER_LAUNCHER sccache)
        message(STATUS "Enabling sccache")
    else()
        message(STATUS "Failed to enabling sccache")
    endif()
endif ()

if (ENABLE_ABC)
    add_compile_definitions(YOSYS_ENABLE_ABC)
    if (LINK_ABC)
        add_compile_definitions(YOSYS_LINK_ABC)
        target_link_libraries(yosys_obj PUBLIC $<TARGET_FILE:libabc>)
        add_dependencies(yosys_obj libabc)
    endif()        
endif()

if (ENABLE_PLUGINS)
    find_package(LibFFI REQUIRED)
    add_compile_definitions(YOSYS_ENABLE_PLUGINS)
    include_directories(${LIBFFI_INCLUDE_DIR})
    target_link_libraries(yosys_obj PUBLIC ${LIBFFI_LIBRARY})
endif()

if (DISABLE_SPAWN)
    add_compile_definitions(YOSYS_DISABLE_SPAWN)
endif()

function(add_share_file _dir _name)
    install(FILES ${_name} DESTINATION ${_dir})
endfunction()

function(add_gen_share_file _dir _name)
    add_share_file("${_dir}" "${_name}")
endfunction()

function(add_include_file _dir _name)
    add_share_file("share/include/${_dir}" "${_name}")
endfunction()


add_subdirectory(kernel)
add_subdirectory(libs)

add_subdirectory(frontends/aiger)
add_subdirectory(frontends/aiger2)
add_subdirectory(frontends/ast)
add_subdirectory(frontends/blif)
add_subdirectory(frontends/json)
add_subdirectory(frontends/liberty)
add_subdirectory(frontends/rpc)
add_subdirectory(frontends/rtlil)
add_subdirectory(frontends/verific)
add_subdirectory(frontends/verilog)

add_subdirectory(backends/aiger)
add_subdirectory(backends/aiger2)
add_subdirectory(backends/blif)
add_subdirectory(backends/btor)
add_subdirectory(backends/cxxrtl)
add_subdirectory(backends/edif)
add_subdirectory(backends/firrtl)
add_subdirectory(backends/functional)
add_subdirectory(backends/intersynth)
add_subdirectory(backends/jny)
add_subdirectory(backends/json)
add_subdirectory(backends/rtlil)
add_subdirectory(backends/simplec)
add_subdirectory(backends/smt2)
add_subdirectory(backends/smv)
add_subdirectory(backends/spice)
add_subdirectory(backends/table)
add_subdirectory(backends/verilog)

add_subdirectory(passes/cmds)
add_subdirectory(passes/equiv)
add_subdirectory(passes/fsm)
add_subdirectory(passes/hierarchy)
add_subdirectory(passes/memory)
add_subdirectory(passes/opt)
add_subdirectory(passes/pmgen)
add_subdirectory(passes/proc)
add_subdirectory(passes/sat)
add_subdirectory(passes/techmap)
add_subdirectory(passes/tests)

add_subdirectory(techlibs/achronix)
add_subdirectory(techlibs/anlogic)
add_subdirectory(techlibs/common)
add_subdirectory(techlibs/coolrunner2)
add_subdirectory(techlibs/easic)
add_subdirectory(techlibs/ecp5)
add_subdirectory(techlibs/efinix)
add_subdirectory(techlibs/fabulous)
add_subdirectory(techlibs/gatemate)
add_subdirectory(techlibs/gowin)
add_subdirectory(techlibs/greenpak4)
add_subdirectory(techlibs/ice40)
add_subdirectory(techlibs/intel)
add_subdirectory(techlibs/intel_alm)
add_subdirectory(techlibs/lattice)
add_subdirectory(techlibs/microchip)
add_subdirectory(techlibs/nanoxplore)
add_subdirectory(techlibs/nexus)
add_subdirectory(techlibs/quicklogic)
add_subdirectory(techlibs/sf2)
add_subdirectory(techlibs/xilinx)

add_include_file("kernel" "kernel/binding.h")
add_include_file("kernel" "kernel/bitpattern.h")
add_include_file("kernel" "kernel/cellaigs.h")
add_include_file("kernel" "kernel/celledges.h")
add_include_file("kernel" "kernel/celltypes.h")
add_include_file("kernel" "kernel/consteval.h")
add_include_file("kernel" "kernel/constids.inc")
add_include_file("kernel" "kernel/cost.h")
add_include_file("kernel" "kernel/drivertools.h")
add_include_file("kernel" "kernel/ff.h")
add_include_file("kernel" "kernel/ffinit.h")
add_include_file("kernel" "kernel/ffmerge.h")
add_include_file("kernel" "kernel/fmt.h")
add_include_file("kernel" "kernel/hashlib.h")
add_include_file("kernel" "kernel/json.h")
add_include_file("kernel" "kernel/log.h")
add_include_file("kernel" "kernel/macc.h")
add_include_file("kernel" "kernel/modtools.h")
add_include_file("kernel" "kernel/mem.h")
add_include_file("kernel" "kernel/qcsat.h")
add_include_file("kernel" "kernel/register.h")
add_include_file("kernel" "kernel/rtlil.h")
add_include_file("kernel" "kernel/satgen.h")
add_include_file("kernel" "kernel/scopeinfo.h")
add_include_file("kernel" "kernel/sexpr.h")
add_include_file("kernel" "kernel/sigtools.h")
add_include_file("kernel" "kernel/timinginfo.h")
add_include_file("kernel" "kernel/utils.h")
add_include_file("kernel" "kernel/yosys.h")
add_include_file("kernel" "kernel/yosys_common.h")
add_include_file("kernel" "kernel/yw.h")
add_include_file("libs/ezsat" "libs/ezsat/ezsat.h")
add_include_file("libs/ezsat" "libs/ezsat/ezminisat.h")
add_include_file("libs/sha1" "libs/sha1/sha1.h")
add_include_file("libs/json11" "libs/json11/json11.hpp")
add_include_file("passes/fsm" "passes/fsm/fsmdata.h")
add_include_file("frontends/ast" "frontends/ast/ast.h")
add_include_file("frontends/ast" "frontends/ast/ast_binding.h")
add_include_file("frontends/blif" "frontends/blif/blifparse.h")
add_include_file("backends/rtlil" "backends/rtlil/rtlil_backend.h")

if (ENABLE_ZLIB)
    add_include_file("kernel" "kernel/fstdata.h")
    add_include_file("libs/fst" "libs/fst/fstapi.h")
endif()

set_property(SOURCE kernel/log.cc APPEND PROPERTY COMPILE_DEFINITIONS YOSYS_SRC="${PROJECT_SOURCE_DIR}")

if (ENABLE_LIBYOSYS)
    add_library(yosys_shared SHARED
        $<TARGET_OBJECTS:yosys_obj>
    )
    target_link_libraries(yosys_shared PUBLIC yosys_obj)
    # set_target_properties(yosys_shared PROPERTIES OUTPUT_NAME yosys)
    install(TARGETS yosys_shared
            LIBRARY DESTINATION lib)
endif()

add_executable(yosys_exe
    kernel/driver.cc
    $<TARGET_OBJECTS:yosys_obj>
)
target_link_libraries(yosys_exe PUBLIC yosys_obj)
set_target_properties(yosys_exe PROPERTIES OUTPUT_NAME yosys)
install(TARGETS yosys_exe
        RUNTIME DESTINATION bin)

#### yosys-config setup ####
include(cmake/YosysConfig.cmake)

#### INSTALL ####
if (ENABLE_ABC)
    install(PROGRAMS $<TARGET_FILE:abc>
            DESTINATION bin
            RENAME yosys-abc)
endif()

install(PROGRAMS ${yosys_BINARY_DIR}/yosys-config DESTINATION bin)

#### TESTING ####
include(cmake/TestFiles.cmake)
enable_testing()

set(_YOSYS_TEST_ENV
    "PATH=${PROJECT_SOURCE_DIR}:$ENV{PATH};")

foreach(dir IN LISTS SH_TEST_DIRS)
    string(REPLACE "/" "_" name "${dir}")
    add_test(
        NAME    seed-tests.${name}
        COMMAND bash -c
                "cd \"${PROJECT_SOURCE_DIR}/${dir}\" && bash run-test.sh ${SEEDOPT}"
    )
    set_tests_properties(seed-tests.${name} PROPERTIES
                         ENVIRONMENT "${_YOSYS_TEST_ENV}"
                         DEPENDS yosys_exe)
endforeach()

foreach(dir IN LISTS SH_ABC_TEST_DIRS)
    string(REPLACE "/" "_" name "${dir}")
    add_test(
        NAME    abcopt-tests.${name}
        COMMAND bash -c
                "cd \"${PROJECT_SOURCE_DIR}/${dir}\" && bash run-test.sh ${ABCOPT} ${SEEDOPT}"
    )
    set_tests_properties(abcopt-tests.${name} PROPERTIES
                         ENVIRONMENT "${_YOSYS_TEST_ENV}"
                         DEPENDS yosys_exe)
endforeach()

foreach(dir IN LISTS MK_TEST_DIRS)
    string(REPLACE "/" "_" name "${dir}")
    add_test(
        NAME    makefile-tests.${name}
        COMMAND bash -c
                "
                cd \"${PROJECT_SOURCE_DIR}/${dir}\" &&
                bash run-test.sh &&
                ${CMAKE_MAKE_PROGRAM} -f run-test.mk
                "
    )
    set_tests_properties(makefile-tests.${name} PROPERTIES
                         ENVIRONMENT "${_YOSYS_TEST_ENV}"
                         DEPENDS yosys_exe)
endforeach()
