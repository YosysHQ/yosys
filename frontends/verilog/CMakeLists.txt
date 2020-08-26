
BISON_TARGET(VerilogParser  ilang_parser.y ${CMAKE_CURRENT_LIST_DIR}/ilang_parser.tab.cc DEFINES_FILE ${CMAKE_CURRENT_LIST_DIR}/ilang_parser.tab.hh)
FLEX_TARGET (VerilogScanner ilang_lexer.l  ${CMAKE_CURRENT_LIST_DIR}/ilang_lexer.cc)
ADD_FLEX_BISON_DEPENDENCY(VerilogScanner VerilogParser)
SET(VerilogParserSrc
        ${BISON_VerilogParser_OUTPUTS}
        ${FLEX_VerilogScanner_OUTPUTS}
        )
