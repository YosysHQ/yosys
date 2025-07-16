

add_library(yosys_techlibs_fabulous OBJECT
    synth_fabulous.cc
)

target_link_libraries(yosys_obj PUBLIC yosys_techlibs_fabulous)
target_sources(yosys_obj PUBLIC $<TARGET_OBJECTS:yosys_techlibs_fabulous>)

add_share_file("share/fabulous" "cells_map.v")
add_share_file("share/fabulous" "prims.v")
add_share_file("share/fabulous" "latches_map.v")
add_share_file("share/fabulous" "ff_map.v")
add_share_file("share/fabulous" "ram_regfile.txt")
add_share_file("share/fabulous" "regfile_map.v")
add_share_file("share/fabulous" "io_map.v")
add_share_file("share/fabulous" "arith_map.v")
