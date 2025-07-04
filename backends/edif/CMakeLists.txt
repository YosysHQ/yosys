add_library(yosys_backends_edif INTERFACE)

target_sources(yosys_backends_edif INTERFACE
    edif.cc
)

target_link_libraries(yosys PUBLIC yosys_backends_edif)
