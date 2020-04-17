
OBJS += techlibs/intel_alm/synth_intel_alm.o

# Techmap
$(eval $(call add_share_file,share/intel_alm/common,techlibs/intel_alm/common/alm_map.v))
$(eval $(call add_share_file,share/intel_alm/common,techlibs/intel_alm/common/alm_sim.v))
$(eval $(call add_share_file,share/intel_alm/common,techlibs/intel_alm/common/arith_alm_map.v))
$(eval $(call add_share_file,share/intel_alm/common,techlibs/intel_alm/common/dff_map.v))
$(eval $(call add_share_file,share/intel_alm/common,techlibs/intel_alm/common/dff_sim.v))

# RAM
bramtypes := m10k m20k
$(foreach bramtype, $(bramtypes), $(eval $(call add_share_file,share/intel_alm/common,techlibs/intel_alm/common/bram_$(bramtype).txt)))
$(foreach bramtype, $(bramtypes), $(eval $(call add_share_file,share/intel_alm/common,techlibs/intel_alm/common/bram_$(bramtype)_map.v)))
$(eval $(call add_share_file,share/intel_alm/common,techlibs/intel_alm/common/lutram_mlab.txt))
$(eval $(call add_share_file,share/intel_alm/common,techlibs/intel_alm/common/lutram_mlab_map.v))

families := cyclonev cyclone10gx

# Miscellaneous
$(eval $(call add_share_file,share/intel_alm/common,techlibs/intel_alm/common/megafunction_bb.v))
$(eval $(call add_share_file,share/intel_alm/common,techlibs/intel_alm/common/quartus_rename.v))
$(foreach family, $(families), $(eval $(call add_share_file,share/intel_alm/$(family),techlibs/intel_alm/$(family)/quartus_rename.v)))
