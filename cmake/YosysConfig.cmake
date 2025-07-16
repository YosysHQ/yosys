#### yosys-config setup ####
# compiler
get_filename_component(_CXX_BASENAME "${CMAKE_CXX_COMPILER}" NAME)
set(YOSYS_CFG_CXX "${_CXX_BASENAME}"
        CACHE STRING "C++ compiler that appears in yosys-config")

# compile flags
set(_CFG_CXXFLAGS
        -Wall -Wextra -ggdb
        "-I\"${CMAKE_INSTALL_PREFIX}/share/yosys/include\""
        -MD -MP -D_YOSYS_ -fPIC
        -DYOSYS_VERSION="${YOSYS_VER}"
        -std=c++${CXXSTD} -O3)

if (ENABLE_READLINE)
    list(APPEND _CFG_CXXFLAGS -DYOSYS_ENABLE_READLINE)
endif()
if (ENABLE_PLUGINS)
    list(APPEND _CFG_CXXFLAGS -DYOSYS_ENABLE_PLUGINS)
endif()
if (ENABLE_GLOB)
    list(APPEND _CFG_CXXFLAGS -DYOSYS_ENABLE_GLOB)
endif()
if (ENABLE_ZLIB)
    list(APPEND _CFG_CXXFLAGS -DYOSYS_ENABLE_ZLIB)
endif()
if (ENABLE_TCL)
    list(APPEND _CFG_CXXFLAGS -I${TCL_INCLUDE_PATH} -DYOSYS_ENABLE_TCL)
endif()
if (ENABLE_ABC)
    list(APPEND _CFG_CXXFLAGS -DYOSYS_ENABLE_ABC)
endif()
if (ENABLE_COVER)
    list(APPEND _CFG_CXXFLAGS -DYOSYS_ENABLE_COVER)
endif()

string (REPLACE ";" " " YOSYS_CFG_CXXFLAGS "${_CFG_CXXFLAGS}")

# link flags
set(YOSYS_CFG_LINKFLAGS "-rdynamic" CACHE STRING "link flags for yosys-config")

# libraries
set(_CFG_LIBS -lstdc++ -lm)
if (NOT (${CMAKE_SYSTEM_NAME} STREQUAL "OpenBSD"))
    list(APPEND _CFG_LIBS -lrt)
endif()
if (ENABLE_READLINE)
    list(APPEND _CFG_LIBS -lreadline)
endif()
if (ENABLE_PLUGINS)
    list(APPEND _CFG_LIBS -lffi)
    if (NOT APPLE)
        list(APPEND _CFG_LIBS -ldl)
    endif()
endif()
if (ENABLE_ZLIB)
    list(APPEND _CFG_LIBS -lz)
endif()
if (ENABLE_TCL)
    get_filename_component(_TCL "${TCL_LIBRARY}" NAME_WE)
    string(REGEX REPLACE "^lib" "" _TCL "${_TCL}")
    list(APPEND _CFG_LIBS "-l${_TCL}")
endif()
string (REPLACE ";" " " YOSYS_CFG_LIBS "${_CFG_LIBS}")

# bindir / datadir (installation paths)
set(YOSYS_CFG_PREFIX "/usr/local"
    CACHE STRING "prefix that yosys-config reports")

set(YOSYS_CFG_BINDIR "${YOSYS_CFG_PREFIX}/bin")
set(YOSYS_CFG_DATDIR "${YOSYS_CFG_PREFIX}/share/yosys")

# abort if something is missing
foreach(var YOSYS_CFG_CXX YOSYS_CFG_CXXFLAGS YOSYS_CFG_LINKFLAGS
        YOSYS_CFG_LIBS YOSYS_CFG_BINDIR YOSYS_CFG_DATDIR)
    if("${${var}}" STREQUAL "")
        message(FATAL_ERROR "${var} is empty – cannot create yosys-config")
    endif()
endforeach()

set(CXX        "${YOSYS_CFG_CXX}")
set(CXXFLAGS   "${YOSYS_CFG_CXXFLAGS}")
set(LINKFLAGS  "${YOSYS_CFG_LINKFLAGS}")
set(LIBS       "${YOSYS_CFG_LIBS}")
set(BINDIR     "${YOSYS_CFG_BINDIR}")
set(DATDIR     "${YOSYS_CFG_DATDIR}")

configure_file(misc/yosys-config.in ${yosys_BINARY_DIR}/yosys-config @ONLY)
file(CHMOD ${yosys_BINARY_DIR}/yosys-config
        PERMISSIONS OWNER_READ OWNER_WRITE OWNER_EXECUTE
        GROUP_READ GROUP_EXECUTE
        WORLD_READ WORLD_EXECUTE)

add_custom_target(yosys-config-copy ALL
        DEPENDS ${yosys_BINARY_DIR}/yosys-config)