add_library(yosys_techlibs_greenpak4 INTERFACE)

target_sources(yosys_techlibs_greenpak4 INTERFACE
    synth_greenpak4.cc
    greenpak4_dffinv.cc
)

target_link_libraries(yosys PUBLIC yosys_techlibs_greenpak4)

add_share_file("share/greenpak4" "cells_blackbox.v")
add_share_file("share/greenpak4" "cells_latch.v")
add_share_file("share/greenpak4" "cells_map.v")
add_share_file("share/greenpak4" "cells_sim.v")
add_share_file("share/greenpak4" "cells_sim_ams.v")
add_share_file("share/greenpak4" "cells_sim_digital.v")
add_share_file("share/greenpak4" "cells_sim_wip.v")
add_share_file("share/greenpak4" "gp_dff.lib")
