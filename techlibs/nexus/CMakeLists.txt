

add_library(yosys_techlibs_nexus OBJECT
    synth_nexus.cc
)

target_link_libraries(yosys PUBLIC yosys_techlibs_nexus)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_techlibs_nexus>)

add_share_file("share/nexus" "cells_map.v")
add_share_file("share/nexus" "cells_sim.v")
add_share_file("share/nexus" "parse_init.vh")
add_share_file("share/nexus" "cells_xtra.v")
add_share_file("share/nexus" "lutrams_map.v")
add_share_file("share/nexus" "lutrams.txt")
add_share_file("share/nexus" "brams_map.v")
add_share_file("share/nexus" "brams.txt")
add_share_file("share/nexus" "lrams_map.v")
add_share_file("share/nexus" "lrams.txt")
add_share_file("share/nexus" "arith_map.v")
add_share_file("share/nexus" "latches_map.v")
add_share_file("share/nexus" "dsp_map.v")
