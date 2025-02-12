add_library(yosys_techlibs_greenpak4 INTERFACE)

target_sources(yosys_techlibs_greenpak4 INTERFACE
    synth_greenpak4.cc
    greenpak4_dffinv.cc
)

target_link_libraries(yosys PRIVATE yosys_techlibs_greenpak4)
