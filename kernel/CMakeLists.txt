
PROJECT(kernel)

EXECUTE_PROCESS(
        COMMAND git rev-parse --short HEAD
        OUTPUT_VARIABLE GIT_HASH
        ERROR_QUIET
)
STRING(REPLACE "\n" "" YOSYS_VER_STR "${GIT_HASH}")
IF ("${YOSYS_VER_STR}" STREQUAL "")
    SET(YOSYS_VER_STR "UNKNOWN")
ENDIF()
MESSAGE("<< HASH >> ${YOSYS_VER_STR}")
CONFIGURE_FILE(yosys_version.cc.in ${CMAKE_CURRENT_LIST_DIR}/yosys_version.cc @ONLY NEWLINE_STYLE UNIX)

ADD_LIBRARY(${PROJECT_NAME}
        satgen.h
        hashlib.h
        modtools.h
        ff.h
        cellaigs.h
        yosys.h
        log.h
        celledges.h
        cost.h
        macc.h
        utils.h
        register.h
        rtlil.h
        bitpattern.h
        ffinit.h
        consteval.h
        sigtools.h
        timinginfo.h
        celltypes.h

        log.cc
        calc.cc
        satgen.cc
        yosys.cc
        celledges.cc
        driver.cc
        cellaigs.cc
        register.cc
        rtlil.cc
        yosys_version.cc
        yosys_version.cc.in
        )
