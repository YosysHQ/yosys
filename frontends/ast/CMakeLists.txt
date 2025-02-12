add_library(yosys_frontends_ast INTERFACE)

target_sources(yosys_frontends_ast INTERFACE
    ast_binding.cc
    ast_binding.h
    ast.cc
    ast.h
    dpicall.cc
    genrtlil.cc
    simplify.cc
)

target_link_libraries(yosys PRIVATE yosys_frontends_ast)
