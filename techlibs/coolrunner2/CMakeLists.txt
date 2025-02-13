add_library(yosys_techlibs_coolrunner2 INTERFACE)

target_sources(yosys_techlibs_coolrunner2 INTERFACE
    synth_coolrunner2.cc
    coolrunner2_sop.cc
    coolrunner2_fixup.cc
)

target_link_libraries(yosys PRIVATE yosys_techlibs_coolrunner2)

add_share_file("share/coolrunner2" "cells_latch.v")
add_share_file("share/coolrunner2" "cells_sim.v")
add_share_file("share/coolrunner2" "cells_counter_map.v")
add_share_file("share/coolrunner2" "tff_extract.v")
add_share_file("share/coolrunner2" "xc2_dff.lib")
