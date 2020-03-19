
OBJS += techlibs/xilinx/synth_xilinx.o
OBJS += techlibs/xilinx/xilinx_dffopt.o

GENFILES += techlibs/xilinx/brams_init_36.vh
GENFILES += techlibs/xilinx/brams_init_32.vh
GENFILES += techlibs/xilinx/brams_init_18.vh
GENFILES += techlibs/xilinx/brams_init_16.vh
GENFILES += techlibs/xilinx/brams_init_9.vh
GENFILES += techlibs/xilinx/brams_init_8.vh

EXTRA_OBJS += techlibs/xilinx/brams_init.mk
.SECONDARY: techlibs/xilinx/brams_init.mk

techlibs/xilinx/brams_init.mk: techlibs/xilinx/brams_init.py
	$(Q) mkdir -p techlibs/xilinx
	$(P) $(PYTHON_EXECUTABLE) $<
	$(Q) touch $@

techlibs/xilinx/brams_init_36.vh: techlibs/xilinx/brams_init.mk
techlibs/xilinx/brams_init_32.vh: techlibs/xilinx/brams_init.mk
techlibs/xilinx/brams_init_18.vh: techlibs/xilinx/brams_init.mk
techlibs/xilinx/brams_init_16.vh: techlibs/xilinx/brams_init.mk
techlibs/xilinx/brams_init_9.vh: techlibs/xilinx/brams_init.mk
techlibs/xilinx/brams_init_8.vh: techlibs/xilinx/brams_init.mk

$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/cells_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/cells_sim.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/cells_xtra.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc2v_brams.txt))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc2v_brams_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc3sa_brams.txt))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc3sda_brams.txt))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc6s_brams.txt))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc6s_brams_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc7_xcu_brams.txt))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc7_brams_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xcu_brams_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xcup_urams.txt))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xcup_urams_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/lut4_lutrams.txt))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/lut6_lutrams.txt))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/lutrams_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/arith_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc6s_ff_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc7_ff_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/lut_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/mux_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc3s_mult_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc3sda_dsp_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc6s_dsp_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc4v_dsp_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc5v_dsp_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc7_dsp_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xcu_dsp_map.v))

$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/abc9_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/abc9_unmap.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/abc9_model.v))

$(eval $(call add_gen_share_file,share/xilinx,techlibs/xilinx/brams_init_36.vh))
$(eval $(call add_gen_share_file,share/xilinx,techlibs/xilinx/brams_init_32.vh))
$(eval $(call add_gen_share_file,share/xilinx,techlibs/xilinx/brams_init_18.vh))
$(eval $(call add_gen_share_file,share/xilinx,techlibs/xilinx/brams_init_16.vh))
$(eval $(call add_gen_share_file,share/xilinx,techlibs/xilinx/brams_init_9.vh))
$(eval $(call add_gen_share_file,share/xilinx,techlibs/xilinx/brams_init_8.vh))

