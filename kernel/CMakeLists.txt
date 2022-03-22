
#PROJECT(kernel)

# YOSYS_VER
SET(YOSYS_VER "0.9+3491")
# GIT_REV
EXECUTE_PROCESS(COMMAND git rev-parse --short HEAD OUTPUT_VARIABLE GIT_HASH ERROR_QUIET)
STRING(REPLACE "\n" "" GIT_REV "${GIT_HASH}")
IF ("${GIT_REV}" STREQUAL "")
    SET(GIT_REV "UNKNOWN")
ENDIF()
MESSAGE("<< HASH >> ${GIT_REV}")
# CXX_NAME
get_filename_component(CXX_NAME ${CMAKE_CXX_COMPILER} NAME)
# CXX_VER
SET(CXX_VER ${CMAKE_CXX_COMPILER_VERSION})
# # CC_FLAGS_THUMB
CONFIGURE_FILE(yosys_version.cc.in ${CMAKE_CURRENT_LIST_DIR}/yosys_version.cc @ONLY NEWLINE_STYLE UNIX)

SET(_KERNEL_SRC
        bitpattern.h
        calc.cc
        cellaigs.cc
        cellaigs.h
        celledges.cc
        celledges.h
        celltypes.h
        consteval.h
        cost.h
        driver.cc
        ff.h
        ffinit.h
        hashlib.h
        log.cc
        log.h
        macc.h
        modtools.h
        register.cc
        register.h
        rtlil.cc
        rtlil.h
        satgen.cc
        satgen.h
        sigtools.h
        timinginfo.h
        utils.h
        yosys.cc
        yosys.h
        yosys_version.cc
        yosys_version.cc.in
        )

FOREACH(SRC ${_KERNEL_SRC})
    LIST(APPEND KERNEL_SRC ${CMAKE_CURRENT_LIST_DIR}/${SRC})
ENDFOREACH()
SET(KERNEL_SRC ${KERNEL_SRC} PARENT_SCOPE)

MACRO(ConfigSource WORKING_DIRECTORY)
ENDMACRO()

#ADD_LIBRARY(${PROJECT_NAME} ${KERNEL_SRC})
