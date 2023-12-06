techlibs/quicklogic/qlf_k6n10f/bram_types_sim.v: techlibs/quicklogic/qlf_k6n10f/generate_bram_types_sim.py
	$(P) mkdir -p $(dir $@) && $(PYTHON_EXECUTABLE) $^ $@

OBJS += techlibs/quicklogic/synth_quicklogic.o
OBJS += techlibs/quicklogic/ql_bram_merge.o
OBJS += techlibs/quicklogic/ql_bram_types.o
OBJS += techlibs/quicklogic/ql_dsp_simd.o
OBJS += techlibs/quicklogic/ql_dsp_io_regs.o

# --------------------------------------

OBJS += techlibs/quicklogic/ql_dsp_macc.o
GENFILES += techlibs/quicklogic/ql_dsp_macc_pm.h techlibs/quicklogic/qlf_k6n10f/bram_types_sim.v
techlibs/quicklogic/ql_dsp_macc.o: techlibs/quicklogic/ql_dsp_macc_pm.h
$(eval $(call add_extra_objs,techlibs/quicklogic/ql_dsp_macc_pm.h))

# --------------------------------------

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
$(eval $(call add_share_file,share/quicklogic/qlf_k6n10f,techlibs/quicklogic/qlf_k6n10f/brams_sim.v))
$(eval $(call add_gen_share_file,share/quicklogic/qlf_k6n10f,techlibs/quicklogic/qlf_k6n10f/bram_types_sim.v))
$(eval $(call add_share_file,share/quicklogic/qlf_k6n10f,techlibs/quicklogic/qlf_k6n10f/cells_sim.v))
$(eval $(call add_share_file,share/quicklogic/qlf_k6n10f,techlibs/quicklogic/qlf_k6n10f/ffs_map.v))
$(eval $(call add_share_file,share/quicklogic/qlf_k6n10f,techlibs/quicklogic/qlf_k6n10f/dsp_sim.v))
$(eval $(call add_share_file,share/quicklogic/qlf_k6n10f,techlibs/quicklogic/qlf_k6n10f/dsp_map.v))
$(eval $(call add_share_file,share/quicklogic/qlf_k6n10f,techlibs/quicklogic/qlf_k6n10f/dsp_final_map.v))
$(eval $(call add_share_file,share/quicklogic/qlf_k6n10f,techlibs/quicklogic/qlf_k6n10f/TDP18K_FIFO.v))
$(eval $(call add_share_file,share/quicklogic/qlf_k6n10f,techlibs/quicklogic/qlf_k6n10f/ufifo_ctl.v))
$(eval $(call add_share_file,share/quicklogic/qlf_k6n10f,techlibs/quicklogic/qlf_k6n10f/sram1024x18_mem.v))