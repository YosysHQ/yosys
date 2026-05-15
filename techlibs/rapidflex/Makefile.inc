# cell lib generation
techlibs/rapidflex/alkaidC/cell_sim_pcnt.v: techlibs/rapidflex/util/pcnt_cell_sim_gen.py
	$(P) mkdir -p $(dir $@) && $(PYTHON_EXECUTABLE) $^ --file $@

CXXFLAGS += -Itechlibs/rapidflex/src/pugixml.hpp
OBJS += techlibs/rapidflex/src/pugixml.o
OBJS += techlibs/rapidflex/src/synth_rapidflex.o
OBJS += techlibs/rapidflex/src/clock_buffer_cmd.o

# --------------------------------------

OBJS += techlibs/rapidflex/src/rf_new_dsp.o
OBJS += techlibs/rapidflex/src/rf_dsp_mad.o
GENFILES += techlibs/rapidflex/src/rf_new_dsp_pm.h techlibs/rapidflex/src/rf_dsp_mad_pm.h techlibs/rapidflex/alkaidC/cell_sim_pcnt.v
techlibs/rapidflex/src/rf_new_dsp.o: techlibs/rapidflex/src/rf_new_dsp_pm.h
techlibs/rapidflex/src/rf_dsp_mad.o: techlibs/rapidflex/src/rf_dsp_mad_pm.h
$(eval $(call add_extra_objs,techlibs/rapidflex/src/rf_new_dsp_pm.h,techlibs/rapidflex/src/rf_dsp_mad_pm.h))

# --------------------------------------

$(eval $(call add_share_file,share/rapidflex/common,techlibs/rapidflex/common/cells_sim.v))

# --------------AlkaidC cell lib ------------------------
$(eval $(call add_share_file,share/rapidflex/alkaidC,techlibs/rapidflex/alkaidC/arith_map.v))
$(eval $(call add_share_file,share/rapidflex/alkaidC,techlibs/rapidflex/alkaidC/ccb_inst_code.v))
$(eval $(call add_share_file,share/rapidflex/alkaidC,techlibs/rapidflex/alkaidC/cell_sim_arith.v))
$(eval $(call add_share_file,share/rapidflex/alkaidC,techlibs/rapidflex/alkaidC/cell_sim_ccb.v))
$(eval $(call add_share_file,share/rapidflex/alkaidC,techlibs/rapidflex/alkaidC/cell_sim_ff.v))
$(eval $(call add_share_file,share/rapidflex/alkaidC,techlibs/rapidflex/alkaidC/cell_sim_pcnt.v))
$(eval $(call add_share_file,share/rapidflex/alkaidC,techlibs/rapidflex/alkaidC/cell_sim.v))
$(eval $(call add_share_file,share/rapidflex/alkaidC,techlibs/rapidflex/alkaidC/dff_map.v))
$(eval $(call add_gen_share_file,share/rapidflex/alkaidC,techlibs/rapidflex/alkaidC/cell_sim_pcnt.v))

$(eval $(call add_share_file,share/rapidflex/alkaidL,techlibs/rapidflex/alkaidL/arith_map.v))
$(eval $(call add_share_file,share/rapidflex/alkaidL,techlibs/rapidflex/alkaidL/bram_map.v))
$(eval $(call add_share_file,share/rapidflex/alkaidL,techlibs/rapidflex/alkaidL/bram.txt))
$(eval $(call add_share_file,share/rapidflex/alkaidL,techlibs/rapidflex/alkaidL/cell_sim_arith.v))
$(eval $(call add_share_file,share/rapidflex/alkaidL,techlibs/rapidflex/alkaidL/cell_sim_bram.v))
$(eval $(call add_share_file,share/rapidflex/alkaidL,techlibs/rapidflex/alkaidL/cell_sim_dsp.v))
$(eval $(call add_share_file,share/rapidflex/alkaidL,techlibs/rapidflex/alkaidL/cell_sim_ff.v))
$(eval $(call add_share_file,share/rapidflex/alkaidL,techlibs/rapidflex/alkaidL/cell_sim.v))
$(eval $(call add_share_file,share/rapidflex/alkaidL,techlibs/rapidflex/alkaidL/dff_map.v))
$(eval $(call add_share_file,share/rapidflex/alkaidL,techlibs/rapidflex/alkaidL/dsp_map.v))

$(eval $(call add_share_file,share/rapidflex/alkaidT,techlibs/rapidflex/alkaidT/arith_map.v))
$(eval $(call add_share_file,share/rapidflex/alkaidT,techlibs/rapidflex/alkaidT/bram_map.v))
$(eval $(call add_share_file,share/rapidflex/alkaidT,techlibs/rapidflex/alkaidT/bram.txt))
$(eval $(call add_share_file,share/rapidflex/alkaidT,techlibs/rapidflex/alkaidT/cell_sim_arith.v))
$(eval $(call add_share_file,share/rapidflex/alkaidT,techlibs/rapidflex/alkaidT/cell_sim_bram.v))
$(eval $(call add_share_file,share/rapidflex/alkaidT,techlibs/rapidflex/alkaidT/cell_sim_dsp.v))
$(eval $(call add_share_file,share/rapidflex/alkaidT,techlibs/rapidflex/alkaidT/cell_sim_new_dsp.v))
$(eval $(call add_share_file,share/rapidflex/alkaidT,techlibs/rapidflex/alkaidT/cell_sim_ff.v))
$(eval $(call add_share_file,share/rapidflex/alkaidT,techlibs/rapidflex/alkaidT/cell_sim.v))
$(eval $(call add_share_file,share/rapidflex/alkaidT,techlibs/rapidflex/alkaidT/dff_map.v))
$(eval $(call add_share_file,share/rapidflex/alkaidT,techlibs/rapidflex/alkaidT/dsp_map.v))
