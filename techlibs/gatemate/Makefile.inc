
OBJS += techlibs/gatemate/synth_gatemate.o
OBJS += techlibs/gatemate/gatemate_foldinv.o

$(eval $(call add_share_file,share/gatemate,techlibs/gatemate/reg_map.v))
$(eval $(call add_share_file,share/gatemate,techlibs/gatemate/mux_map.v))
$(eval $(call add_share_file,share/gatemate,techlibs/gatemate/lut_map.v))
$(eval $(call add_share_file,share/gatemate,techlibs/gatemate/mul_map.v))
$(eval $(call add_share_file,share/gatemate,techlibs/gatemate/arith_map.v))
$(eval $(call add_share_file,share/gatemate,techlibs/gatemate/cells_sim.v))
$(eval $(call add_share_file,share/gatemate,techlibs/gatemate/cells_bb.v))
$(eval $(call add_share_file,share/gatemate,techlibs/gatemate/brams_map.v))
$(eval $(call add_share_file,share/gatemate,techlibs/gatemate/brams.txt))
$(eval $(call add_share_file,share/gatemate,techlibs/gatemate/brams_init_20.vh))
$(eval $(call add_share_file,share/gatemate,techlibs/gatemate/brams_init_40.vh))
$(eval $(call add_share_file,share/gatemate,techlibs/gatemate/inv_map.v))

EXTRA_OBJS += techlibs/gatemate/lut_tree_lib.mk
.SECONDARY: techlibs/gatemate/lut_tree_lib.mk

techlibs/gatemate/lut_tree_lib.mk: techlibs/gatemate/make_lut_tree_lib.py
	$(Q) mkdir -p techlibs/gatemate
	$(P) $(PYTHON_EXECUTABLE) $<
	$(Q) touch $@

techlibs/gatemate/lut_tree_cells.genlib: techlibs/gatemate/lut_tree_lib.mk
techlibs/gatemate/lut_tree_map.v: techlibs/gatemate/lut_tree_lib.mk

$(eval $(call add_gen_share_file,share/gatemate,techlibs/gatemate/lut_tree_cells.genlib))
$(eval $(call add_gen_share_file,share/gatemate,techlibs/gatemate/lut_tree_map.v))
