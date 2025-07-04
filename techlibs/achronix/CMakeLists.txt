add_library(yosys_techlibs_achronix INTERFACE)

target_sources(yosys_techlibs_achronix INTERFACE
    synth_achronix.cc
)

target_link_libraries(yosys PUBLIC yosys_techlibs_achronix)

add_share_file("share/achronix/speedster22i" "speedster22i/cells_sim.v")
add_share_file("share/achronix/speedster22i" "speedster22i/cells_map.v")
