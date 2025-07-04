add_library(yosys_techlibs_easic INTERFACE)

target_sources(yosys_techlibs_easic INTERFACE
    synth_easic.cc
)

target_link_libraries(yosys PUBLIC yosys_techlibs_easic)
