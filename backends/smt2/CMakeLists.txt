add_library(yosys_backends_smt2 INTERFACE)

target_sources(yosys_backends_smt2 INTERFACE
    smt2.cc
)

target_link_libraries(yosys PRIVATE yosys_backends_smt2)
