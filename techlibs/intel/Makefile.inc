
OBJS += techlibs/intel/synth_intel.o

$(eval $(call add_share_file,share/intel/common,techlibs/intel/common/m9k_bb.v))
$(eval $(call add_share_file,share/intel/common,techlibs/intel/common/altpll_bb.v))
$(eval $(call add_share_file,share/intel/common,techlibs/intel/common/brams_m9k.txt))
$(eval $(call add_share_file,share/intel/common,techlibs/intel/common/brams_map_m9k.v))

# Add the cell models and mappings for the VQM backend
families := max10 arria10gx cyclonev cyclone10lp cycloneiv cycloneive
$(foreach family,$(families), $(eval $(call add_share_file,share/intel/$(family),techlibs/intel/$(family)/cells_sim.v)))
$(foreach family,$(families), $(eval $(call add_share_file,share/intel/$(family),techlibs/intel/$(family)/cells_map.v)))
#$(eval $(call add_share_file,share/intel/cycloneive,techlibs/intel/cycloneive/arith_map.v))

