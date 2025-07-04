add_library(yosys_backends_table INTERFACE)

target_sources(yosys_backends_table INTERFACE
    table.cc
)

target_link_libraries(yosys PUBLIC yosys_backends_table)
