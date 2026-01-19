
OBJS += techlibs/intel_alm/synth_intel_alm.o

# Techmap
$(eval $(call add_share_file,share/intel_alm/common,techlibs/intel_alm/common/abc9_map.v))
$(eval $(call add_share_file,share/intel_alm/common,techlibs/intel_alm/common/abc9_unmap.v))
$(eval $(call add_share_file,share/intel_alm/common,techlibs/intel_alm/common/abc9_model.v))
$(eval $(call add_share_file,share/intel_alm/common,techlibs/intel_alm/common/alm_map.v))
$(eval $(call add_share_file,share/intel_alm/common,techlibs/intel_alm/common/alm_sim.v))
$(eval $(call add_share_file,share/intel_alm/common,techlibs/intel_alm/common/arith_alm_map.v))
$(eval $(call add_share_file,share/intel_alm/common,techlibs/intel_alm/common/dff_map.v))
$(eval $(call add_share_file,share/intel_alm/common,techlibs/intel_alm/common/dff_sim.v))
$(eval $(call add_share_file,share/intel_alm/common,techlibs/intel_alm/common/dsp_sim.v))
$(eval $(call add_share_file,share/intel_alm/common,techlibs/intel_alm/common/dsp_map.v))
$(eval $(call add_share_file,share/intel_alm/common,techlibs/intel_alm/common/mem_sim.v))
$(eval $(call add_share_file,share/intel_alm/common,techlibs/intel_alm/common/misc_sim.v))

$(eval $(call add_share_file,share/intel_alm/cyclonev,techlibs/intel_alm/cyclonev/cells_sim.v))

# RAM
$(eval $(call add_share_file,share/intel_alm/common,techlibs/intel_alm/common/bram_m10k.txt))
$(eval $(call add_share_file,share/intel_alm/common,techlibs/intel_alm/common/bram_m10k_map.v))
$(eval $(call add_share_file,share/intel_alm/common,techlibs/intel_alm/common/lutram_mlab.txt))

# Miscellaneous
$(eval $(call add_share_file,share/intel_alm/common,techlibs/intel_alm/common/megafunction_bb.v))
