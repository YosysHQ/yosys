
BISON_TARGET(ILangParser  ilang_parser.y ${CMAKE_CURRENT_LIST_DIR}/ilang_parser.tab.cc
        COMPILE_FLAGS "-d -r all -b frontends/ilang/ilang_parser"
        DEFINES_FILE ${CMAKE_CURRENT_LIST_DIR}/ilang_parser.tab.hh
        )
FLEX_TARGET (ILangScanner ilang_lexer.l  ${CMAKE_CURRENT_LIST_DIR}/ilang_lexer.cc)
ADD_FLEX_BISON_DEPENDENCY(ILangScanner ILangParser)
SET(ILangParserSrc
        ${BISON_ILangParser_OUTPUTS}
        ${FLEX_ILangScanner_OUTPUTS}
        )
