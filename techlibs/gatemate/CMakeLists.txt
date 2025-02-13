add_library(yosys_techlibs_gatemate INTERFACE)

target_sources(yosys_techlibs_gatemate INTERFACE
    synth_gatemate.cc
    gatemate_foldinv.cc
)

target_link_libraries(yosys PRIVATE yosys_techlibs_gatemate)

add_share_file("share/gatemate" "reg_map.v")
add_share_file("share/gatemate" "mux_map.v")
add_share_file("share/gatemate" "lut_map.v")
add_share_file("share/gatemate" "mul_map.v")
add_share_file("share/gatemate" "arith_map.v")
add_share_file("share/gatemate" "cells_sim.v")
add_share_file("share/gatemate" "cells_bb.v")
add_share_file("share/gatemate" "brams_map.v")
add_share_file("share/gatemate" "brams.txt")
add_share_file("share/gatemate" "brams_init_20.vh")
add_share_file("share/gatemate" "brams_init_40.vh")
add_share_file("share/gatemate" "inv_map.v")
