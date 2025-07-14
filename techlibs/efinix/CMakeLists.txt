

add_library(yosys_techlibs_efinix OBJECT
    synth_efinix.cc
    efinix_fixcarry.cc
)

target_link_libraries(yosys PUBLIC yosys_techlibs_efinix)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_techlibs_efinix>)

add_share_file("share/efinix" "cells_map.v")
add_share_file("share/efinix" "arith_map.v")
add_share_file("share/efinix" "cells_sim.v")
add_share_file("share/efinix" "brams_map.v")
add_share_file("share/efinix" "gbuf_map.v")
add_share_file("share/efinix" "brams.txt")
