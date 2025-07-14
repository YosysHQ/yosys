#add_custom_command(
#        COMMAND ${CMAKE_COMMAND} -E make_directory ${CMAKE_CURRENT_BINARY_DIR}
#        OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/verilog_parser.tab.cc ${CMAKE_CURRENT_BINARY_DIR}/verilog_parser.tab.hh
#        COMMAND ${BISON_EXECUTABLE}
#        -Wall -Werror
#        -o verilog_parser.tab.cc
#        -d -r all
#        ${CMAKE_CURRENT_SOURCE_DIR}/verilog_parser.y
#        DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/verilog_parser.y
#        COMMENT "Generating frontends/verilog/verilog_parser.tab.cc"
#        VERBATIM
#        COMMAND_EXPAND_LISTS
#)
#
#add_custom_command(
#        COMMAND ${CMAKE_COMMAND} -E make_directory ${CMAKE_CURRENT_BINARY_DIR}
#        OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/verilog_lexer.cc
#        COMMAND ${FLEX_EXECUTABLE}
#        --outfile=verilog_lexer.cc
#        ${CMAKE_CURRENT_SOURCE_DIR}/verilog_lexer.l
#        DEPENDS ${CMAKE_CURRENT_SOURCE_DIR}/verilog_lexer.l
#        COMMENT "Generating frontends/verilog/verilog_lexer.cc"
#        VERBATIM
#        COMMAND_EXPAND_LISTS
#)

flex_target(VERILOG_LEXER "verilog_lexer.l" "${CMAKE_CURRENT_BINARY_DIR}/verilog_lexer.cc")
bison_target(VERILOG_PARSER "verilog_parser.y" "${CMAKE_CURRENT_BINARY_DIR}/verilog_parser.tab.cc" DEFINES_FILE "${CMAKE_CURRENT_BINARY_DIR}/verilog_parser.tab.hh" COMPILE_FLAGS "-Wall -Werror -d -r all")


add_library(yosys_frontends_verilog OBJECT
    const2ast.cc
    preproc.cc
    preproc.h
    verilog_frontend.cc
    verilog_frontend.h
)

add_library(yosys_frontends_verilog_gen OBJECT
    ${FLEX_VERILOG_LEXER_OUTPUTS}
    ${BISON_VERILOG_PARSER_OUTPUTS}
    #${CMAKE_CURRENT_BINARY_DIR}/verilog_lexer.cc
    #${CMAKE_CURRENT_BINARY_DIR}/verilog_parser.tab.cc
    #${CMAKE_CURRENT_BINARY_DIR}/verilog_parser.tab.hh
)
target_link_libraries(yosys PUBLIC yosys_frontends_verilog yosys_frontends_verilog_gen)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_frontends_verilog>)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_frontends_verilog_gen>)
