add_library(yosys_techlibs_ecp5 INTERFACE)

target_sources(yosys_techlibs_ecp5 INTERFACE
    synth_ecp5.cc
)

target_link_libraries(yosys PRIVATE yosys_techlibs_ecp5)
