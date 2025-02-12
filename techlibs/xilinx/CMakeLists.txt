add_library(yosys_techlibs_xilinx INTERFACE)

target_sources(yosys_techlibs_xilinx INTERFACE
    synth_xilinx.cc
    xilinx_dffopt.cc
)

target_link_libraries(yosys PRIVATE yosys_techlibs_xilinx)
