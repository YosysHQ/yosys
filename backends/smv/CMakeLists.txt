add_library(yosys_backends_smv INTERFACE)

target_sources(yosys_backends_smv INTERFACE
    smv.cc
)

target_link_libraries(yosys PUBLIC yosys_backends_smv)
