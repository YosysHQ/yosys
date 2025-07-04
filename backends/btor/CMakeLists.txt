add_library(yosys_backends_btor INTERFACE)

target_sources(yosys_backends_btor INTERFACE
    btor.cc
)

target_link_libraries(yosys PUBLIC yosys_backends_btor)
