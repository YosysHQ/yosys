
OBJS += techlibs/xilinx/synth_xilinx.o

GENFILES += techlibs/xilinx/brams_init_36.vh
GENFILES += techlibs/xilinx/brams_init_32.vh
GENFILES += techlibs/xilinx/brams_init_18.vh
GENFILES += techlibs/xilinx/brams_init_16.vh

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

$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/cells_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/cells_sim.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/cells_xtra.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/brams.txt))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/brams_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/brams_bb.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/drams.txt))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/drams_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/drams_bb.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/arith_map.v))

$(eval $(call add_gen_share_file,share/xilinx,techlibs/xilinx/brams_init_36.vh))
$(eval $(call add_gen_share_file,share/xilinx,techlibs/xilinx/brams_init_32.vh))
$(eval $(call add_gen_share_file,share/xilinx,techlibs/xilinx/brams_init_18.vh))
$(eval $(call add_gen_share_file,share/xilinx,techlibs/xilinx/brams_init_16.vh))

