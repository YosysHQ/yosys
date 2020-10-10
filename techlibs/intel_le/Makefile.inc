
OBJS += techlibs/intel_le/synth_intel_le.o

# Techmap
$(eval $(call add_share_file,share/intel_le/common,techlibs/intel_le/common/abc9_map.v))
$(eval $(call add_share_file,share/intel_le/common,techlibs/intel_le/common/abc9_unmap.v))
$(eval $(call add_share_file,share/intel_le/common,techlibs/intel_le/common/abc9_model.v))
$(eval $(call add_share_file,share/intel_le/common,techlibs/intel_le/common/alm_map.v))
$(eval $(call add_share_file,share/intel_le/common,techlibs/intel_le/common/alm_sim.v))
$(eval $(call add_share_file,share/intel_le/common,techlibs/intel_le/common/arith_alm_map.v))
$(eval $(call add_share_file,share/intel_le/common,techlibs/intel_le/common/dff_map.v))
$(eval $(call add_share_file,share/intel_le/common,techlibs/intel_le/common/dff_sim.v))
$(eval $(call add_share_file,share/intel_le/common,techlibs/intel_le/common/dsp_sim.v))
$(eval $(call add_share_file,share/intel_le/common,techlibs/intel_le/common/dsp_map.v))
$(eval $(call add_share_file,share/intel_le/common,techlibs/intel_le/common/mem_sim.v))

$(eval $(call add_share_file,share/intel_le/cyclonev,techlibs/intel_le/cycloneiv/cells_sim.v))

# RAM
$(eval $(call add_share_file,share/intel_le/common,techlibs/intel_le/common/bram_m10k.txt))
$(eval $(call add_share_file,share/intel_le/common,techlibs/intel_le/common/bram_m20k.txt))
$(eval $(call add_share_file,share/intel_le/common,techlibs/intel_le/common/bram_m20k_map.v))
$(eval $(call add_share_file,share/intel_le/common,techlibs/intel_le/common/lutram_mlab.txt))

# Miscellaneous
$(eval $(call add_share_file,share/intel_le/common,techlibs/intel_le/common/megafunction_bb.v))
$(eval $(call add_share_file,share/intel_le/common,techlibs/intel_le/common/quartus_rename.v))
