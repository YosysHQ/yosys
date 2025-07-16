

add_library(yosys_techlibs_achronix OBJECT
    synth_achronix.cc
)

target_link_libraries(yosys_obj PUBLIC yosys_techlibs_achronix)
target_sources(yosys_obj PUBLIC $<TARGET_OBJECTS:yosys_techlibs_achronix>)

add_share_file("share/achronix/speedster22i" "speedster22i/cells_sim.v")
add_share_file("share/achronix/speedster22i" "speedster22i/cells_map.v")
