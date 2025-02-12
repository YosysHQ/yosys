add_library(yosys_techlibs_efinix INTERFACE)

target_sources(yosys_techlibs_efinix INTERFACE
    synth_efinix.cc
    efinix_fixcarry.cc
)

target_link_libraries(yosys PRIVATE yosys_techlibs_efinix)
