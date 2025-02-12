add_library(yosys_techlibs_ice40 INTERFACE)

target_sources(yosys_techlibs_ice40 INTERFACE
    synth_ice40.cc
    ice40_braminit.cc
    ice40_opt.cc
)

target_link_libraries(yosys PRIVATE yosys_techlibs_ice40)
