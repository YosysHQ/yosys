
OBJS += techlibs/ice40/synth_ice40.o
OBJS += techlibs/ice40/ice40_braminit.o
OBJS += techlibs/ice40/ice40_opt.o

$(eval $(call add_share_file,share/ice40,techlibs/ice40/arith_map.v))
$(eval $(call add_share_file,share/ice40,techlibs/ice40/cells_map.v))
$(eval $(call add_share_file,share/ice40,techlibs/ice40/ff_map.v))
$(eval $(call add_share_file,share/ice40,techlibs/ice40/cells_sim.v))
$(eval $(call add_share_file,share/ice40,techlibs/ice40/latches_map.v))
$(eval $(call add_share_file,share/ice40,techlibs/ice40/brams.txt))
$(eval $(call add_share_file,share/ice40,techlibs/ice40/brams_map.v))
$(eval $(call add_share_file,share/ice40,techlibs/ice40/spram.txt))
$(eval $(call add_share_file,share/ice40,techlibs/ice40/spram_map.v))
$(eval $(call add_share_file,share/ice40,techlibs/ice40/dsp_map.v))
$(eval $(call add_share_file,share/ice40,techlibs/ice40/abc9_model.v))

OBJS += techlibs/ice40/ice40_dsp.o
GENFILES += techlibs/ice40/ice40_dsp_pm.h
techlibs/ice40/ice40_dsp.o: techlibs/ice40/ice40_dsp_pm.h
$(eval $(call add_extra_objs,techlibs/ice40/ice40_dsp_pm.h))

OBJS += techlibs/ice40/ice40_wrapcarry.o
GENFILES += techlibs/ice40/ice40_wrapcarry_pm.h
techlibs/ice40/ice40_wrapcarry.o: techlibs/ice40/ice40_wrapcarry_pm.h
$(eval $(call add_extra_objs,techlibs/ice40/ice40_wrapcarry_pm.h))
