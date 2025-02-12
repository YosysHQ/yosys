add_library(yosys_techlibs_sf2 INTERFACE)

target_sources(yosys_techlibs_sf2 INTERFACE
    synth_sf2.cc
)

target_link_libraries(yosys PRIVATE yosys_techlibs_sf2)
