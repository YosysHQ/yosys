
OBJS += techlibs/machxo2/synth_machxo2.o

$(eval $(call add_share_file,share/machxo2,techlibs/machxo2/cells_map.v))
$(eval $(call add_share_file,share/machxo2,techlibs/machxo2/cells_sim.v))
