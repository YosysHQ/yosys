add_library(yosys_backends_spice INTERFACE)

target_sources(yosys_backends_spice INTERFACE
    spice.cc
)

target_link_libraries(yosys PUBLIC yosys_backends_spice)
