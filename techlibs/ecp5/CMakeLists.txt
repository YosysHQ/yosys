

add_library(yosys_techlibs_ecp5 OBJECT
    synth_ecp5.cc
)

target_link_libraries(yosys_obj PUBLIC yosys_techlibs_ecp5)
target_sources(yosys_obj PUBLIC $<TARGET_OBJECTS:yosys_techlibs_ecp5>)

add_share_file("share/ecp5" "cells_ff.vh")
add_share_file("share/ecp5" "cells_io.vh")
add_share_file("share/ecp5" "cells_map.v")
add_share_file("share/ecp5" "cells_sim.v")
add_share_file("share/ecp5" "cells_bb.v")
add_share_file("share/ecp5" "lutrams_map.v")
add_share_file("share/ecp5" "lutrams.txt")
add_share_file("share/ecp5" "brams_map.v")
add_share_file("share/ecp5" "brams.txt")
add_share_file("share/ecp5" "arith_map.v")
add_share_file("share/ecp5" "latches_map.v")
add_share_file("share/ecp5" "dsp_map.v")
