
OBJS += techlibs/intel/synth_intel.o

$(eval $(call add_share_file,share/intel/common,techlibs/intel/common/m9k_bb.v))
$(eval $(call add_share_file,share/intel/common,techlibs/intel/common/altpll_bb.v))
$(eval $(call add_share_file,share/intel/common,techlibs/intel/common/brams.txt))
$(eval $(call add_share_file,share/intel/common,techlibs/intel/common/brams_map.v))
$(eval $(call add_share_file,share/intel/max10,techlibs/intel/max10/cells_sim.v))
$(eval $(call add_share_file,share/intel/a10gx,techlibs/intel/a10gx/cells_sim.v))
$(eval $(call add_share_file,share/intel/cyclonev,techlibs/intel/cyclonev/cells_sim.v))
$(eval $(call add_share_file,share/intel/cyclone10,techlibs/intel/cyclone10/cells_sim.v))
$(eval $(call add_share_file,share/intel/cycloneiv,techlibs/intel/cycloneiv/cells_sim.v))
$(eval $(call add_share_file,share/intel/cycloneive,techlibs/intel/cycloneive/cells_sim.v))
$(eval $(call add_share_file,share/intel/max10,techlibs/intel/max10/cells_map.v))
$(eval $(call add_share_file,share/intel/a10gx,techlibs/intel/a10gx/cells_map.v))
$(eval $(call add_share_file,share/intel/cyclonev,techlibs/intel/cyclonev/cells_map.v))
$(eval $(call add_share_file,share/intel/cyclone10,techlibs/intel/cyclone10/cells_map.v))
$(eval $(call add_share_file,share/intel/cycloneiv,techlibs/intel/cycloneiv/cells_map.v))
$(eval $(call add_share_file,share/intel/cycloneive,techlibs/intel/cycloneive/cells_map.v))
#$(eval $(call add_share_file,share/intel/max10,techlibs/intel/max10/arith_map.v))
#$(eval $(call add_share_file,share/intel/a10gx,techlibs/intel/a10gx/arith_map.v))
#$(eval $(call add_share_file,share/intel/cycloneiv,techlibs/intel/cycloneiv/arith_map.v))
#$(eval $(call add_share_file,share/intel/cycloneive,techlibs/intel/cycloneive/arith_map.v))

