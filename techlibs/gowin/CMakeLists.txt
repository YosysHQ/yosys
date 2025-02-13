add_library(yosys_techlibs_gowin INTERFACE)

target_sources(yosys_techlibs_gowin INTERFACE
    synth_gowin.cc
)

target_link_libraries(yosys PRIVATE yosys_techlibs_gowin)

add_share_file("share/gowin" "cells_map.v")
add_share_file("share/gowin" "cells_sim.v")
add_share_file("share/gowin" "cells_xtra_gw1n.v")
add_share_file("share/gowin" "cells_xtra_gw2a.v")
add_share_file("share/gowin" "cells_xtra_gw5a.v")
add_share_file("share/gowin" "arith_map.v")
add_share_file("share/gowin" "brams_map.v")
add_share_file("share/gowin" "brams.txt")
add_share_file("share/gowin" "lutrams_map.v")
add_share_file("share/gowin" "lutrams.txt")
