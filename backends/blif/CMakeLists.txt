add_library(yosys_backends_blif INTERFACE)

target_sources(yosys_backends_blif INTERFACE
    blif.cc
)

target_link_libraries(yosys PUBLIC yosys_backends_blif)
