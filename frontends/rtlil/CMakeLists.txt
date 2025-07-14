flex_target(RTLIL_LEXER "rtlil_lexer.l" "${CMAKE_CURRENT_BINARY_DIR}/rtlil_lexer.cc")
bison_target(RTLIL_PARSER "rtlil_parser.y" "${CMAKE_CURRENT_BINARY_DIR}/rtlil_parser.tab.cc" DEFINES_FILE "${CMAKE_CURRENT_BINARY_DIR}/rtlil_parser.tab.hh" COMPILE_FLAGS "-d -r all")


add_library(yosys_frontends_rtlil OBJECT
    rtlil_frontend.cc
)

add_library(yosys_frontends_rtlil_gen OBJECT
    #${CMAKE_CURRENT_BINARY_DIR}/rtlil_lexer.cc
    #${CMAKE_CURRENT_BINARY_DIR}/rtlil_parser.tab.cc
    #${CMAKE_CURRENT_BINARY_DIR}/rtlil_parser.tab.hh
    ${FLEX_RTLIL_LEXER_OUTPUTS}
    ${BISON_RTLIL_PARSER_OUTPUTS}
)
target_link_libraries(yosys PUBLIC yosys_frontends_rtlil yosys_frontends_rtlil_gen)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_frontends_rtlil>)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_frontends_rtlil_gen>)
