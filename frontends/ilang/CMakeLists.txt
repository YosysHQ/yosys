
MACRO(CONFIG_ILANG_FLEX_BISON WORKING_DIRECTORY)
    BISON_TARGET(ILangParser
            ${WORKING_DIRECTORY}/ilang_parser.y
            ${WORKING_DIRECTORY}/ilang_parser.tab.cc
            COMPILE_FLAGS "-Wall -Werror -d -r all -b ilang_parser"
            DEFINES_FILE ${WORKING_DIRECTORY}/ilang_parser.tab.hh
            )
    FLEX_TARGET (ILangScanner
            ${WORKING_DIRECTORY}/ilang_lexer.l
            ${WORKING_DIRECTORY}/ilang_lexer.cc
            )
    ADD_FLEX_BISON_DEPENDENCY(ILangScanner ILangParser)
ENDMACRO()

SET(ILangParserSrc
        ${CMAKE_CURRENT_LIST_DIR}/ilang_parser.tab.cc
        ${CMAKE_CURRENT_LIST_DIR}/ilang_parser.tab.hh
        ${CMAKE_CURRENT_LIST_DIR}/ilang_lexer.cc
        PARENT_SCOPE
        )
