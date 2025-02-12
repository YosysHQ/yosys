add_library(yosys_backends_simplec INTERFACE)

target_sources(yosys_backends_simplec INTERFACE
    simplec.cc
)

target_link_libraries(yosys PRIVATE yosys_backends_simplec)
