

add_library(yosys_frontends_ast OBJECT
    ast_binding.cc
    ast_binding.h
    ast.cc
    ast.h
    dpicall.cc
    genrtlil.cc
    simplify.cc
)

target_link_libraries(yosys PUBLIC yosys_frontends_ast)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_frontends_ast>)
