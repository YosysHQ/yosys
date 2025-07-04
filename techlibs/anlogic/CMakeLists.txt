add_library(yosys_techlibs_anlogic INTERFACE)

target_sources(yosys_techlibs_anlogic INTERFACE
    synth_anlogic.cc
    anlogic_eqn.cc
    anlogic_fixcarry.cc
)

target_link_libraries(yosys PUBLIC yosys_techlibs_anlogic)

add_share_file("share/anlogic" "cells_map.v")
add_share_file("share/anlogic" "arith_map.v")
add_share_file("share/anlogic" "cells_sim.v")
add_share_file("share/anlogic" "eagle_bb.v")
add_share_file("share/anlogic" "lutrams.txt")
add_share_file("share/anlogic" "lutrams_map.v")
add_share_file("share/anlogic" "brams.txt")
add_share_file("share/anlogic" "brams_map.v")
