
OBJS += techlibs/achronix/synth_achronix.o

$(eval $(call add_share_file,share/achronix/speedster22i/,techlibs/achronix/speedster22i/cells_sim.v))
$(eval $(call add_share_file,share/achronix/speedster22i/,techlibs/achronix/speedster22i/cells_map.v))

