add_library(yosys_techlibs_intel INTERFACE)

target_sources(yosys_techlibs_intel INTERFACE
    synth_intel.cc
)

target_link_libraries(yosys PRIVATE yosys_techlibs_intel)
