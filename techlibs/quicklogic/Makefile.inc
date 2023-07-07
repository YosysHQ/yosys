OBJS += techlibs/quicklogic/synth_quicklogic.o

$(eval $(call add_share_file,share/quicklogic/common,techlibs/quicklogic/common/cells_sim.v))

$(eval $(call add_share_file,share/quicklogic/pp3,techlibs/quicklogic/pp3/ffs_map.v))
$(eval $(call add_share_file,share/quicklogic/pp3,techlibs/quicklogic/pp3/lut_map.v))
$(eval $(call add_share_file,share/quicklogic/pp3,techlibs/quicklogic/pp3/latches_map.v))
$(eval $(call add_share_file,share/quicklogic/pp3,techlibs/quicklogic/pp3/cells_map.v))
$(eval $(call add_share_file,share/quicklogic/pp3,techlibs/quicklogic/pp3/cells_sim.v))
$(eval $(call add_share_file,share/quicklogic/pp3,techlibs/quicklogic/pp3/abc9_model.v))
$(eval $(call add_share_file,share/quicklogic/pp3,techlibs/quicklogic/pp3/abc9_map.v))
$(eval $(call add_share_file,share/quicklogic/pp3,techlibs/quicklogic/pp3/abc9_unmap.v))
