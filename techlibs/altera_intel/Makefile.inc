
OBJS += techlibs/altera_intel/synth_intel.o

#$(eval $(call add_share_file,share/altera_intel,techlibs/altera_intel/lpm_functions.v))
$(eval $(call add_share_file,share/altera_intel/max10,techlibs/altera_intel/max10/cells_comb_max10.v))
$(eval $(call add_share_file,share/altera_intel/cycloneiv,techlibs/altera_intel/cycloneiv/cells_comb_cycloneiv.v))
$(eval $(call add_share_file,share/altera_intel/max10,techlibs/altera_intel/max10/cells_map_max10.v))
$(eval $(call add_share_file,share/altera_intel/cycloneiv,techlibs/altera_intel/cycloneiv/cells_map_cycloneiv.v))
#$(eval $(call add_share_file,share/altera_intel/max10,techlibs/altera_intel/max10/cells_arith_max10.v))

