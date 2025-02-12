add_library(yosys_backends_btor INTERFACE)

target_sources(yosys_backends_btor INTERFACE
    btor.cc
)

target_link_libraries(yosys PRIVATE yosys_backends_btor)
