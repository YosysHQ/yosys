

add_library(yosys_techlibs_sf2 OBJECT
    synth_sf2.cc
)

target_link_libraries(yosys_obj PUBLIC yosys_techlibs_sf2)
target_sources(yosys_obj PUBLIC $<TARGET_OBJECTS:yosys_techlibs_sf2>)

add_share_file("share/sf2" "arith_map.v")
add_share_file("share/sf2" "cells_map.v")
add_share_file("share/sf2" "cells_sim.v")
