
OBJS += techlibs/quicklogic/synth_quicklogic.o

$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/cells_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/cells_sim.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/FIFO_16K_BLK.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/RAM_16K_BLK.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/MULT_16BIT_X2.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/MULT_32BIT.v))