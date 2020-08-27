
MACRO(CONFIG_VERILOG_FLEX_BISON WORKING_DIRECTORY)
    BISON_TARGET(VerilogParser
            ${WORKING_DIRECTORY}/verilog_parser.y
            ${WORKING_DIRECTORY}/verilog_parser.tab.cc
            COMPILE_FLAGS "-Wall -Werror -d -r all -b verilog_parser"
            DEFINES_FILE ${WORKING_DIRECTORY}/verilog_parser.tab.hh
            )
    FLEX_TARGET (VerilogScanner
            ${WORKING_DIRECTORY}/verilog_lexer.l
            ${WORKING_DIRECTORY}/verilog_lexer.cc
            )
    ADD_FLEX_BISON_DEPENDENCY(VerilogScanner VerilogParser)
ENDMACRO()

SET(VerilogParserSrc
        ${CMAKE_CURRENT_LIST_DIR}/verilog_parser.tab.cc
        ${CMAKE_CURRENT_LIST_DIR}/verilog_parser.tab.hh
        ${CMAKE_CURRENT_LIST_DIR}/verilog_lexer.cc
        PARENT_SCOPE
        )
