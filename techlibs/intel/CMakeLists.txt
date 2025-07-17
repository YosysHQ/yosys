

add_library(yosys_techlibs_intel OBJECT
    synth_intel.cc
)

target_link_libraries(yosys_obj PUBLIC yosys_techlibs_intel)
target_sources(yosys_obj PUBLIC $<TARGET_OBJECTS:yosys_techlibs_intel>)

add_share_file("share/intel/common" "common/m9k_bb.v")
add_share_file("share/intel/common" "common/altpll_bb.v")
add_share_file("share/intel/common" "common/brams_m9k.txt")
add_share_file("share/intel/common" "common/brams_map_m9k.v")
add_share_file("share/intel/common" "common/ff_map.v")

# Add the cell models and mappings for the VQM backend
foreach(family IN ITEMS max10 cyclone10lp cycloneiv cycloneive)
    add_share_file("share/intel/${family}" "${family}/cells_sim.v")
    add_share_file("share/intel/${family}" "${family}/cells_map.v")
endforeach()
