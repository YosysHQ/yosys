add_library(yosys_techlibs_ice40 INTERFACE)

target_sources(yosys_techlibs_ice40 INTERFACE
    synth_ice40.cc
    ice40_braminit.cc
    ice40_opt.cc
)

target_link_libraries(yosys PRIVATE yosys_techlibs_ice40)

add_share_file("share/ice40" "arith_map.v")
add_share_file("share/ice40" "cells_map.v")
add_share_file("share/ice40" "ff_map.v")
add_share_file("share/ice40" "cells_sim.v")
add_share_file("share/ice40" "latches_map.v")
add_share_file("share/ice40" "brams.txt")
add_share_file("share/ice40" "brams_map.v")
add_share_file("share/ice40" "spram.txt")
add_share_file("share/ice40" "spram_map.v")
add_share_file("share/ice40" "dsp_map.v")
add_share_file("share/ice40" "abc9_model.v")
