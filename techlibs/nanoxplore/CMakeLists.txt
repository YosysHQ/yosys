

add_library(yosys_techlibs_nanoxplore OBJECT
    synth_nanoxplore.cc
    nx_carry.cc
)

target_link_libraries(yosys PUBLIC yosys_techlibs_nanoxplore)
target_sources(yosys PUBLIC $<TARGET_OBJECTS:yosys_techlibs_nanoxplore>)

# Techmap
add_share_file("share/nanoxplore" "arith_map.v")
add_share_file("share/nanoxplore" "brams_init.vh")
add_share_file("share/nanoxplore" "brams_map.v")
add_share_file("share/nanoxplore" "brams.txt")
add_share_file("share/nanoxplore" "cells_bb.v")
add_share_file("share/nanoxplore" "cells_bb_l.v")
add_share_file("share/nanoxplore" "cells_bb_m.v")
add_share_file("share/nanoxplore" "cells_bb_u.v")
add_share_file("share/nanoxplore" "cells_map.v")
add_share_file("share/nanoxplore" "cells_sim.v")
add_share_file("share/nanoxplore" "cells_sim_l.v")
add_share_file("share/nanoxplore" "cells_sim_m.v")
add_share_file("share/nanoxplore" "cells_sim_u.v")
add_share_file("share/nanoxplore" "cells_wrap.v")
add_share_file("share/nanoxplore" "cells_wrap_l.v")
add_share_file("share/nanoxplore" "cells_wrap_m.v")
add_share_file("share/nanoxplore" "cells_wrap_u.v")
add_share_file("share/nanoxplore" "io_map.v")
add_share_file("share/nanoxplore" "latches_map.v")
add_share_file("share/nanoxplore" "rf_init.vh")
add_share_file("share/nanoxplore" "rf_rams_l.txt")
add_share_file("share/nanoxplore" "rf_rams_m.txt")
add_share_file("share/nanoxplore" "rf_rams_u.txt")
add_share_file("share/nanoxplore" "rf_rams_map_l.v")
add_share_file("share/nanoxplore" "rf_rams_map_m.v")
add_share_file("share/nanoxplore" "rf_rams_map_u.v")
