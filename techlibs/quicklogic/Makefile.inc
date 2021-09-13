OBJS += techlibs/quicklogic/synth_quicklogic.o

$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/pp3_ffs_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/pp3_lut_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/pp3_latches_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/pp3_cells_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/cells_sim.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/lut_sim.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/pp3_cells_sim.v))

$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/abc9_model.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/abc9_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/abc9_unmap.v))
