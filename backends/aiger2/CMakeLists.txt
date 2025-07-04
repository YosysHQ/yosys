add_library(yosys_backends_aiger2 INTERFACE)

target_sources(yosys_backends_aiger2 INTERFACE
    aiger.cc
)

target_link_libraries(yosys PUBLIC yosys_backends_aiger2)
