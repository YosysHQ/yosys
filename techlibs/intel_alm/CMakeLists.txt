add_library(yosys_techlibs_intel_alm INTERFACE)

target_sources(yosys_techlibs_intel_alm INTERFACE
    synth_intel_alm.cc
)

target_link_libraries(yosys PRIVATE yosys_techlibs_intel_alm)
