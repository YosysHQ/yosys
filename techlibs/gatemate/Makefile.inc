
OBJS += techlibs/gatemate/synth_gatemate.o

$(eval $(call add_share_file,share/gatemate,techlibs/gatemate/reg_map.v))
$(eval $(call add_share_file,share/gatemate,techlibs/gatemate/mux_map.v))
$(eval $(call add_share_file,share/gatemate,techlibs/gatemate/lut_map.v))
$(eval $(call add_share_file,share/gatemate,techlibs/gatemate/mul_map.v))
$(eval $(call add_share_file,share/gatemate,techlibs/gatemate/arith_map.v))
$(eval $(call add_share_file,share/gatemate,techlibs/gatemate/cells_sim.v))
$(eval $(call add_share_file,share/gatemate,techlibs/gatemate/cells_bb.v))
$(eval $(call add_share_file,share/gatemate,techlibs/gatemate/brams_map.v))
$(eval $(call add_share_file,share/gatemate,techlibs/gatemate/brams.txt))
$(eval $(call add_share_file,share/gatemate,techlibs/gatemate/brams_init_20.vh))
$(eval $(call add_share_file,share/gatemate,techlibs/gatemate/brams_init_40.vh))
