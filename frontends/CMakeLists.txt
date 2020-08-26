
#PROJECT(frontends)

SET(AIGER_FE_SOURCES
        aiger/aigerparse.cc
        aiger/aigerparse.h
        )

SET(AST_FE_SOURCES
        ast/ast.cc
        ast/ast.h
        ast/dpicall.cc
        ast/genrtlil.cc
        ast/simplify.cc
        )

SET(BLIF_FE_SOURCES
        blif/blifparse.cc
        blif/blifparse.h
        )

SET(ILANG_FE_SOURCES
        ilang/ilang_frontend.cc
        ilang/ilang_frontend.h
        ilang/ilang_lexer.cc
        ilang/ilang_parser.tab.cc
        ilang/ilang_parser.tab.hh
        )

SET(JSON_FE_SOURCES
        json/jsonparse.cc
        )

SET(LIBERTY_FE_SOURCES
        liberty/liberty.cc
        )

SET(RPC_FE_SOURCES
        rpc/rpc_frontend.cc
        )

SET(VERIFIC_FE_SOURCES
        verific/verific.cc
        verific/verific.h
        verific/verificsva.cc
        )

SET(VERILOG_FE_SOURCES
        verilog/const2ast.cc
        verilog/preproc.cc
        verilog/preproc.h
        verilog/verilog_frontend.cc
        verilog/verilog_frontend.h
        verilog/verilog_lexer.cc
        verilog/verilog_parser.tab.cc
        verilog/verilog_parser.tab.hh
        )


SET(FRONTENDS_SRC )
SET(ENABLED_FRONTENDS )

MACRO(ADD_YOSYS_FRONTENDS Name Enabled)
    OPTION(ENABLE_${Name}_FRONTEND "Enable ${Name} frontend." ${Enabled})
    IF (ENABLE_${Name}_FRONTEND)
        FOREACH(SRC ${${Name}_FE_SOURCES})
            LIST(APPEND FRONTENDS_SRC ${CMAKE_CURRENT_LIST_DIR}/${SRC})
        ENDFOREACH()
        LIST(APPEND ENABLED_FRONTENDS ${Name})
    ENDIF()
ENDMACRO()

ADD_YOSYS_FRONTENDS(AIGER       OFF)
ADD_YOSYS_FRONTENDS(AST         ON)
ADD_YOSYS_FRONTENDS(BLIF        ON)
ADD_YOSYS_FRONTENDS(ILANG       ON)
ADD_YOSYS_FRONTENDS(JSON        OFF)
ADD_YOSYS_FRONTENDS(LIBERTY     ON)
ADD_YOSYS_FRONTENDS(RPC         OFF)
ADD_YOSYS_FRONTENDS(VERIFIC     OFF)
ADD_YOSYS_FRONTENDS(VERILOG     ON)

MESSAGE("<< Enabled frontends: ${ENABLED_FRONTENDS} >>")
#ADD_LIBRARY(${PROJECT_NAME} ${FRONTENDS_SRC})
SET(FRONTENDS_SRC ${FRONTENDS_SRC} PARENT_SCOPE)
