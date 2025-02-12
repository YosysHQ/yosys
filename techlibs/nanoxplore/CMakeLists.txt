add_library(yosys_techlibs_nanoxplore INTERFACE)

target_sources(yosys_techlibs_nanoxplore INTERFACE
    synth_nanoxplore.cc
    nx_carry.cc
)

target_link_libraries(yosys PRIVATE yosys_techlibs_nanoxplore)
