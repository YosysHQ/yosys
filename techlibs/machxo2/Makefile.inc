
OBJS += techlibs/machxo2/synth_machxo2.o

$(eval $(call add_share_file,share/machxo2,techlibs/ecp5/cells_io.vh))
$(eval $(call add_share_file,share/machxo2,techlibs/machxo2/cells_map.v))
$(eval $(call add_share_file,share/machxo2,techlibs/machxo2/cells_sim.v))
$(eval $(call add_share_file,share/machxo2,techlibs/machxo2/cells_bb.v))

$(eval $(call add_share_file,share/machxo2,techlibs/ecp5/lutrams.txt))
$(eval $(call add_share_file,share/machxo2,techlibs/ecp5/lutrams_map.v))

$(eval $(call add_share_file,share/machxo2,techlibs/machxo2/brams.txt))
$(eval $(call add_share_file,share/machxo2,techlibs/machxo2/brams_map.v))
$(eval $(call add_share_file,share/machxo2,techlibs/machxo2/arith_map.v))
