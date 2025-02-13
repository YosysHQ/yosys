add_library(yosys_techlibs_xilinx INTERFACE)

target_sources(yosys_techlibs_xilinx INTERFACE
    synth_xilinx.cc
    xilinx_dffopt.cc
)

target_link_libraries(yosys PRIVATE yosys_techlibs_xilinx)

add_share_file("share/xilinx" "cells_map.v")
add_share_file("share/xilinx" "cells_sim.v")
add_share_file("share/xilinx" "cells_xtra.v")

add_share_file("share/xilinx" "lutrams_xcv.txt")
add_share_file("share/xilinx" "lutrams_xcv_map.v")

add_share_file("share/xilinx" "lutrams_xc5v.txt")
add_share_file("share/xilinx" "lutrams_xcu.txt")
add_share_file("share/xilinx" "lutrams_xc5v_map.v")

add_share_file("share/xilinx" "brams_xcv.txt")
add_share_file("share/xilinx" "brams_xcv_map.v")

add_share_file("share/xilinx" "brams_defs.vh")

add_share_file("share/xilinx" "brams_xc2v.txt")
add_share_file("share/xilinx" "brams_xc2v_map.v")

add_share_file("share/xilinx" "brams_xc3sda.txt")
add_share_file("share/xilinx" "brams_xc3sda_map.v")

add_share_file("share/xilinx" "brams_xc4v.txt")
add_share_file("share/xilinx" "brams_xc4v_map.v")
add_share_file("share/xilinx" "brams_xc5v_map.v")
add_share_file("share/xilinx" "brams_xc6v_map.v")
add_share_file("share/xilinx" "brams_xcu_map.v")

add_share_file("share/xilinx" "urams.txt")
add_share_file("share/xilinx" "urams_map.v")

add_share_file("share/xilinx" "arith_map.v")
add_share_file("share/xilinx" "ff_map.v")
add_share_file("share/xilinx" "lut_map.v")
add_share_file("share/xilinx" "mux_map.v")
add_share_file("share/xilinx" "xc3s_mult_map.v")
add_share_file("share/xilinx" "xc3sda_dsp_map.v")
add_share_file("share/xilinx" "xc6s_dsp_map.v")
add_share_file("share/xilinx" "xc4v_dsp_map.v")
add_share_file("share/xilinx" "xc5v_dsp_map.v")
add_share_file("share/xilinx" "xc7_dsp_map.v")
add_share_file("share/xilinx" "xcu_dsp_map.v")

add_share_file("share/xilinx" "abc9_model.v")
