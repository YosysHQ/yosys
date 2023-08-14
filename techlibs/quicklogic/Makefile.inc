OBJS += techlibs/quicklogic/synth_quicklogic.o
OBJS += techlibs/quicklogic/ql-bram-merge.o
OBJS += techlibs/quicklogic/ql-bram-types.o

$(eval $(call add_share_file,share/quicklogic/common,techlibs/quicklogic/common/cells_sim.v))

$(eval $(call add_share_file,share/quicklogic/pp3,techlibs/quicklogic/pp3/ffs_map.v))
$(eval $(call add_share_file,share/quicklogic/pp3,techlibs/quicklogic/pp3/lut_map.v))
$(eval $(call add_share_file,share/quicklogic/pp3,techlibs/quicklogic/pp3/latches_map.v))
$(eval $(call add_share_file,share/quicklogic/pp3,techlibs/quicklogic/pp3/cells_map.v))
$(eval $(call add_share_file,share/quicklogic/pp3,techlibs/quicklogic/pp3/cells_sim.v))
$(eval $(call add_share_file,share/quicklogic/pp3,techlibs/quicklogic/pp3/abc9_model.v))
$(eval $(call add_share_file,share/quicklogic/pp3,techlibs/quicklogic/pp3/abc9_map.v))
$(eval $(call add_share_file,share/quicklogic/pp3,techlibs/quicklogic/pp3/abc9_unmap.v))

$(eval $(call add_share_file,share/quicklogic/qlf_k6n10f,techlibs/quicklogic/qlf_k6n10f/arith_map.v))
$(eval $(call add_share_file,share/quicklogic/qlf_k6n10f,techlibs/quicklogic/qlf_k6n10f/libmap_brams.txt))
$(eval $(call add_share_file,share/quicklogic/qlf_k6n10f,techlibs/quicklogic/qlf_k6n10f/libmap_brams_map.v))
$(eval $(call add_share_file,share/quicklogic/qlf_k6n10f,techlibs/quicklogic/qlf_k6n10f/brams_map.v))
$(eval $(call add_share_file,share/quicklogic/qlf_k6n10f,techlibs/quicklogic/qlf_k6n10f/brams_final_map.v))
$(eval $(call add_share_file,share/quicklogic/qlf_k6n10f,techlibs/quicklogic/qlf_k6n10f/brams_sim.v))
$(eval $(call add_share_file,share/quicklogic/qlf_k6n10f,techlibs/quicklogic/qlf_k6n10f/bram_types_sim.v))
$(eval $(call add_share_file,share/quicklogic/qlf_k6n10f,techlibs/quicklogic/qlf_k6n10f/cells_sim.v))
$(eval $(call add_share_file,share/quicklogic/qlf_k6n10f,techlibs/quicklogic/qlf_k6n10f/ffs_map.v))