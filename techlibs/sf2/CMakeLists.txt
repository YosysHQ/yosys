add_library(yosys_techlibs_sf2 INTERFACE)

target_sources(yosys_techlibs_sf2 INTERFACE
    synth_sf2.cc
)

target_link_libraries(yosys PUBLIC yosys_techlibs_sf2)

add_share_file("share/sf2" "arith_map.v")
add_share_file("share/sf2" "cells_map.v")
add_share_file("share/sf2" "cells_sim.v")
