add_library(yosys_backends_aiger INTERFACE)

target_sources(yosys_backends_aiger INTERFACE
    aiger.cc
    xaiger.cc
)

target_link_libraries(yosys PRIVATE yosys_backends_aiger)
