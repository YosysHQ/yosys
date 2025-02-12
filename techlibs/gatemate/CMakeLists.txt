add_library(yosys_techlibs_gatemate INTERFACE)

target_sources(yosys_techlibs_gatemate INTERFACE
    synth_gatemate.cc
    gatemate_foldinv.cc
)

target_link_libraries(yosys PRIVATE yosys_techlibs_gatemate)
