add_library(yosys_techlibs_nexus INTERFACE)

target_sources(yosys_techlibs_nexus INTERFACE
    synth_nexus.cc
)

target_link_libraries(yosys PRIVATE yosys_techlibs_nexus)
