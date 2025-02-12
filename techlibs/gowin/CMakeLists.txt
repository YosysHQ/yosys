add_library(yosys_techlibs_gowin INTERFACE)

target_sources(yosys_techlibs_gowin INTERFACE
    synth_gowin.cc
)

target_link_libraries(yosys PRIVATE yosys_techlibs_gowin)
