
OBJS += techlibs/quicklogic/synth_quicklogic.o
OBJS += techlibs/quicklogic/quicklogic_eqn.o

$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/pp3_ffs_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/pp3_lut_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/pp3_latches_map.v))
GENFILES += techlibs/quicklogic/bram_init_8_16.vh
GENFILES += techlibs/quicklogic/bram_init_32.vh

$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/pp3_cells_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/pp3_brams.txt))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/pp3_brams_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/cells_sim.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/pp3_cells_sim.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/FIFO_16K_BLK.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/RAM_16K_BLK.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/MULT_16BIT_X2.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/MULT_32BIT.v))
