add_library(yosys_techlibs_intel_alm INTERFACE)

target_sources(yosys_techlibs_intel_alm INTERFACE
    synth_intel_alm.cc
)

target_link_libraries(yosys PUBLIC yosys_techlibs_intel_alm)

# Techmap
add_share_file("share/intel_alm/common" "common/abc9_map.v")
add_share_file("share/intel_alm/common" "common/abc9_unmap.v")
add_share_file("share/intel_alm/common" "common/abc9_model.v")
add_share_file("share/intel_alm/common" "common/alm_map.v")
add_share_file("share/intel_alm/common" "common/alm_sim.v")
add_share_file("share/intel_alm/common" "common/arith_alm_map.v")
add_share_file("share/intel_alm/common" "common/dff_map.v")
add_share_file("share/intel_alm/common" "common/dff_sim.v")
add_share_file("share/intel_alm/common" "common/dsp_sim.v")
add_share_file("share/intel_alm/common" "common/dsp_map.v")
add_share_file("share/intel_alm/common" "common/mem_sim.v")
add_share_file("share/intel_alm/common" "common/misc_sim.v")

add_share_file("share/intel_alm/cyclonev" "cyclonev/cells_sim.v")

# RAM
add_share_file("share/intel_alm/common" "common/bram_m10k.txt")
add_share_file("share/intel_alm/common" "common/bram_m10k_map.v")
add_share_file("share/intel_alm/common" "common/lutram_mlab.txt")

# Miscellaneous
add_share_file("share/intel_alm/common" "common/megafunction_bb.v")
