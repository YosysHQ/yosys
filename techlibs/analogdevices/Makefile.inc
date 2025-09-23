
OBJS += techlibs/analogdevices/synth_analogdevices.o

$(eval $(call add_share_file,share/analogdevices,techlibs/analogdevices/cells_map.v))
$(eval $(call add_share_file,share/analogdevices,techlibs/analogdevices/cells_sim.v))
$(eval $(call add_share_file,share/analogdevices,techlibs/analogdevices/cells_xtra.v))

$(eval $(call add_share_file,share/analogdevices,techlibs/analogdevices/lutrams.txt))
$(eval $(call add_share_file,share/analogdevices,techlibs/analogdevices/lutrams_map.v))

$(eval $(call add_share_file,share/analogdevices,techlibs/analogdevices/brams_defs.vh))

$(eval $(call add_share_file,share/analogdevices,techlibs/analogdevices/brams.txt))
$(eval $(call add_share_file,share/analogdevices,techlibs/analogdevices/brams_map.v))

$(eval $(call add_share_file,share/analogdevices,techlibs/analogdevices/arith_map.v))
$(eval $(call add_share_file,share/analogdevices,techlibs/analogdevices/ff_map.v))
$(eval $(call add_share_file,share/analogdevices,techlibs/analogdevices/lut_map.v))
$(eval $(call add_share_file,share/analogdevices,techlibs/analogdevices/mux_map.v))
$(eval $(call add_share_file,share/analogdevices,techlibs/analogdevices/dsp_map.v))

$(eval $(call add_share_file,share/analogdevices,techlibs/analogdevices/abc9_model.v))
