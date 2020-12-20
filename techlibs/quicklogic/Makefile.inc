OBJS += techlibs/quicklogic/synth_quicklogic.o
#OBJS += techlibs/quicklogic/ap3_opt.o
OBJS += techlibs/quicklogic/quicklogic_eqn.o
OBJS += techlibs/quicklogic/pp3_braminit.o
#OBJS += techlibs/quicklogic/quicklogic_fixcarry.o

GENFILES += techlibs/quicklogic/bram_init_8_16.vh
GENFILES += techlibs/quicklogic/bram_init_32.vh

$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/ap3_ffs_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/ap3_openfpga_ffs_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/ap2_ffs_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/ap_ffs_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/pp3_ffs_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/ap3_lut_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/ap2_lut_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/ap_lut_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/pp3_lut_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/ap3_latches_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/ap2_latches_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/ap_latches_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/pp3_latches_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/ap3_cells_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/ap_cells_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/ap2_cells_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/pp3_cells_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/ap3_arith_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/ap2_arith_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/ap2_io_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/ap2_io_map_dbuff.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/ap3_io_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/ap3_io_map_dbuff.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/ap_io_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/ap_io_map_dbuff.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/cells_sim.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/lut_sim.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/pp3_cells_sim.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/ap3_cells_sim.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/ap2_cells_sim.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/ap_cells_sim.v))

$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/MULT_16BIT_X2.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/MULT_32BIT.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/abc9_model.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/abc9_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/abc9_unmap.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/pp3_brams.txt))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/pp3_brams_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/pp3_mul_map.v))

$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/pp3_lutdefs.txt))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/ap_lutdefs.txt))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/ap2_lutdefs.txt))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/ap3_lutdefs.txt))

$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/openfpga_cells_sim.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/openfpga_arith_map.v))
$(eval $(call add_share_file,share/quicklogic,techlibs/quicklogic/abc9_softadder_model.v))

EXTRA_OBJS += techlibs/quicklogic/brams_init.mk 
.SECONDARY: techlibs/quicklogic/brams_init.mk 

techlibs/quicklogic/brams_init.mk: techlibs/quicklogic/brams_init.py
	$(Q) mkdir -p techlibs/quicklogic
	$(P) $(PYTHON_EXECUTABLE) $<
	$(Q) touch $@


techlibs/quicklogic/bram_init_8_16.vh: techlibs/quicklogic/brams_init.mk
techlibs/quicklogic/bram_init_32.vh: techlibs/quicklogic/brams_init.mk

$(eval $(call add_gen_share_file,share/quicklogic,techlibs/quicklogic/bram_init_8_16.vh))
$(eval $(call add_gen_share_file,share/quicklogic,techlibs/quicklogic/bram_init_32.vh))
