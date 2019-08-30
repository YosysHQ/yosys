
OBJS += techlibs/ecp5/synth_ecp5.o techlibs/ecp5/ecp5_ffinit.o \
        techlibs/ecp5/ecp5_gsr.o

$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/cells_ff.vh))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/cells_io.vh))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/cells_map.v))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/cells_sim.v))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/cells_bb.v))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/lutrams_map.v))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/lutram.txt))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/brams_map.v))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/bram.txt))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/arith_map.v))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/latches_map.v))

$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/abc_map.v))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/abc_unmap.v))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/abc_model.v))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/abc_5g.box))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/abc_5g.lut))
$(eval $(call add_share_file,share/ecp5,techlibs/ecp5/abc_5g_nowide.lut))

EXTRA_OBJS += techlibs/ecp5/brams_init.mk techlibs/ecp5/brams_connect.mk
.SECONDARY: techlibs/ecp5/brams_init.mk techlibs/ecp5/brams_connect.mk

techlibs/ecp5/brams_init.mk: techlibs/ecp5/brams_init.py
	$(Q) mkdir -p techlibs/ecp5
	$(P) python3 $<
	$(Q) touch $@

techlibs/ecp5/brams_connect.mk: techlibs/ecp5/brams_connect.py
	$(Q) mkdir -p techlibs/ecp5
	$(P) python3 $<
	$(Q) touch $@


techlibs/ecp5/bram_init_1_2_4.vh: techlibs/ecp5/brams_init.mk
techlibs/ecp5/bram_init_9_18_36.vh: techlibs/ecp5/brams_init.mk

techlibs/ecp5/bram_conn_1.vh: techlibs/ecp5/brams_connect.mk
techlibs/ecp5/bram_conn_2.vh: techlibs/ecp5/brams_connect.mk
techlibs/ecp5/bram_conn_4.vh: techlibs/ecp5/brams_connect.mk
techlibs/ecp5/bram_conn_9.vh: techlibs/ecp5/brams_connect.mk
techlibs/ecp5/bram_conn_18.vh: techlibs/ecp5/brams_connect.mk

$(eval $(call add_gen_share_file,share/ecp5,techlibs/ecp5/bram_init_1_2_4.vh))
$(eval $(call add_gen_share_file,share/ecp5,techlibs/ecp5/bram_init_9_18_36.vh))

$(eval $(call add_gen_share_file,share/ecp5,techlibs/ecp5/bram_conn_1.vh))
$(eval $(call add_gen_share_file,share/ecp5,techlibs/ecp5/bram_conn_2.vh))
$(eval $(call add_gen_share_file,share/ecp5,techlibs/ecp5/bram_conn_4.vh))
$(eval $(call add_gen_share_file,share/ecp5,techlibs/ecp5/bram_conn_9.vh))
$(eval $(call add_gen_share_file,share/ecp5,techlibs/ecp5/bram_conn_18.vh))
