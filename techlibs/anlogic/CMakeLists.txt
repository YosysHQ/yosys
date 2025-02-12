add_library(yosys_techlibs_anlogic INTERFACE)

target_sources(yosys_techlibs_anlogic INTERFACE
    synth_anlogic.cc
    anlogic_eqn.cc
    anlogic_fixcarry.cc
)

target_link_libraries(yosys PRIVATE yosys_techlibs_anlogic)
