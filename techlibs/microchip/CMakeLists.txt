add_library(yosys_techlibs_microchip INTERFACE)

target_sources(yosys_techlibs_microchip INTERFACE
    synth_microchip.cc
    microchip_dffopt.cc
)

target_link_libraries(yosys PUBLIC yosys_techlibs_microchip)

add_share_file("share/microchip" "arith_map.v")
add_share_file("share/microchip" "cells_map.v")
add_share_file("share/microchip" "cells_sim.v")
add_share_file("share/microchip" "polarfire_dsp_map.v")

add_share_file("share/microchip" "brams_defs.vh")
add_share_file("share/microchip" "LSRAM_map.v")
add_share_file("share/microchip" "LSRAM.txt")
add_share_file("share/microchip" "uSRAM_map.v")
add_share_file("share/microchip" "uSRAM.txt")
