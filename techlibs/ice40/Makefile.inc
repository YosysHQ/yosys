
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
