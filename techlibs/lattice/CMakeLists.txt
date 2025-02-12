add_library(yosys_techlibs_lattice INTERFACE)

target_sources(yosys_techlibs_lattice INTERFACE
    synth_lattice.cc
    lattice_gsr.cc
)

target_link_libraries(yosys PRIVATE yosys_techlibs_lattice)
