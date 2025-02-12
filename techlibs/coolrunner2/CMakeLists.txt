add_library(yosys_techlibs_coolrunner2 INTERFACE)

target_sources(yosys_techlibs_coolrunner2 INTERFACE
    synth_coolrunner2.cc
    coolrunner2_sop.cc
    coolrunner2_fixup.cc
)

target_link_libraries(yosys PRIVATE yosys_techlibs_coolrunner2)
