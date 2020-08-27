PROJECT(backends)

SET(AIGER_BE_SOURCES
        aiger/xaiger.cc
        aiger/aiger.cc
        )

SET(BLIF_BE_SOURCES
        blif/blif.cc
        )

SET(BTOR_BE_SOURCES
        btor/btor.cc
        )

SET(CXXRTL_BE_SOURCES
        cxxrtl/cxxrtl.h
        cxxrtl/cxxrtl_capi.h
        cxxrtl/cxxrtl_vcd.h
        cxxrtl/cxxrtl_vcd_capi.h
        cxxrtl/cxxrtl_capi.cc
        cxxrtl/cxxrtl_vcd_capi.cc
        cxxrtl/cxxrtl_backend.cc
        )

SET(EDIF_BE_SOURCES
        edif/edif.cc
        )

SET(FIRRTL_BE_SOURCES
        firrtl/firrtl.cc
        )

SET(ILANG_BE_SOURCES
        ilang/ilang_backend.h
        ilang/ilang_backend.cc
        )

SET(INTERSYNTH_BE_SOURCES
        intersynth/intersynth.cc
        )

SET(JSON_BE_SOURCES
        json/json.cc
        )

SET(PROTOBUF_BE_SOURCES
        protobuf/protobuf.cc
        )

SET(SIMPLEC_BE_SOURCES
        simplec/simplec.cc
        )

SET(SMT2_BE_SOURCES
        smt2/smt2.cc
        )

SET(SMV_BE_SOURCES
        smv/smv.cc
        )

SET(SPICE_BE_SOURCES
        spice/spice.cc
        )

SET(TABLE_BE_SOURCES
        table/table.cc
        )

SET(VERILOG_BE_SOURCES
        verilog/verilog_backend.cc
        )

SET(BACKENDS_SRC )
SET(ENABLED_BACKENDS )

MACRO(ADD_YOSYS_BACKENDS Name Enabled)
    OPTION(ENABLE_${Name}_BACKEND "Enable ${Name} backend." ${Enabled})
    IF (ENABLE_${Name}_BACKEND)
        FOREACH(SRC ${${Name}_BE_SOURCES})
            LIST(APPEND BACKENDS_SRC ${CMAKE_CURRENT_LIST_DIR}/${SRC})
        ENDFOREACH()
        LIST(APPEND ENABLED_BACKENDS ${Name})
    ENDIF()
ENDMACRO()

ADD_YOSYS_BACKENDS(AIGER      OFF)
ADD_YOSYS_BACKENDS(BLIF       ON)
ADD_YOSYS_BACKENDS(CXXRTL     OFF)
ADD_YOSYS_BACKENDS(EDIF       OFF)
ADD_YOSYS_BACKENDS(FIRRTL     OFF)
ADD_YOSYS_BACKENDS(ILANG      ON)
ADD_YOSYS_BACKENDS(INTERSYNTH OFF)
ADD_YOSYS_BACKENDS(JSON       OFF)
ADD_YOSYS_BACKENDS(PROTOBUF   OFF)
ADD_YOSYS_BACKENDS(SIMPLEC    OFF)
ADD_YOSYS_BACKENDS(SMT2       OFF)
ADD_YOSYS_BACKENDS(SMV        OFF)
ADD_YOSYS_BACKENDS(SPICE      OFF)
ADD_YOSYS_BACKENDS(TABLE      OFF)
ADD_YOSYS_BACKENDS(VERILOG    ON)

MESSAGE("<< Enabled backends: ${ENABLED_BACKENDS} >>")
#ADD_LIBRARY(${PROJECT_NAME} ${BACKENDS_SRC})
SET(BACKENDS_SRC ${BACKENDS_SRC} PARENT_SCOPE)

MACRO(ConfigSource WORKING_DIRECTORY)
ENDMACRO()
