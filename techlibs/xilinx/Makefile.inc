
OBJS += techlibs/xilinx/synth_xilinx.o

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
	$(P) python3 $<
	$(Q) touch $@

techlibs/xilinx/brams_init_36.vh: techlibs/xilinx/brams_init.mk
techlibs/xilinx/brams_init_32.vh: techlibs/xilinx/brams_init.mk
techlibs/xilinx/brams_init_18.vh: techlibs/xilinx/brams_init.mk
techlibs/xilinx/brams_init_16.vh: techlibs/xilinx/brams_init.mk
techlibs/xilinx/brams_init_9.vh: techlibs/xilinx/brams_init.mk
techlibs/xilinx/brams_init_8.vh: techlibs/xilinx/brams_init.mk

$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/cells_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/cells_sim.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc6s_cells_xtra.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc6v_cells_xtra.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc7_cells_xtra.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xcu_cells_xtra.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc6s_brams.txt))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc6s_brams_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc6s_brams_bb.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc7_brams.txt))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc7_brams_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc7_brams_bb.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/lutrams.txt))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/lutrams_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/arith_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc6s_ff_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc7_ff_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/lut_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/mux_map.v))

$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/abc_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/abc_unmap.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/abc_model.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/abc_xc7.box))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/abc_xc7.lut))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/abc_xc7_nowide.lut))

$(eval $(call add_gen_share_file,share/xilinx,techlibs/xilinx/brams_init_36.vh))
$(eval $(call add_gen_share_file,share/xilinx,techlibs/xilinx/brams_init_32.vh))
$(eval $(call add_gen_share_file,share/xilinx,techlibs/xilinx/brams_init_18.vh))
$(eval $(call add_gen_share_file,share/xilinx,techlibs/xilinx/brams_init_16.vh))
$(eval $(call add_gen_share_file,share/xilinx,techlibs/xilinx/brams_init_9.vh))
$(eval $(call add_gen_share_file,share/xilinx,techlibs/xilinx/brams_init_8.vh))

