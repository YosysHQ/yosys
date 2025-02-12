add_library(yosys_techlibs_quicklogic INTERFACE)

target_sources(yosys_techlibs_quicklogic INTERFACE
    synth_quicklogic.cc
    ql_bram_merge.cc
    ql_bram_types.cc
    ql_dsp_simd.cc
    ql_dsp_io_regs.cc
    #ql_dsp_macc.cc
)

target_link_libraries(yosys PRIVATE yosys_techlibs_quicklogic)
