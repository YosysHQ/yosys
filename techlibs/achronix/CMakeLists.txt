add_library(yosys_techlibs_achronix INTERFACE)

target_sources(yosys_techlibs_achronix INTERFACE
    synth_achronix.cc
)

target_link_libraries(yosys PRIVATE yosys_techlibs_achronix)
