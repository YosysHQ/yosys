add_library(yosys_techlibs_microchip INTERFACE)

target_sources(yosys_techlibs_microchip INTERFACE
    synth_microchip.cc
    microchip_dffopt.cc
)

target_link_libraries(yosys PRIVATE yosys_techlibs_microchip)
