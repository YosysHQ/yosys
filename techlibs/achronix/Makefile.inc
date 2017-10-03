
OBJS += techlibs/achronix/synth_speedster.o

$(eval $(call add_share_file,share/achronix/speedster22i/,techlibs/achronix/speedster22i/cells_comb_speedster.v))
$(eval $(call add_share_file,share/achronix/speedster22i/,techlibs/achronix/speedster22i/cells_map_speedster.v))

