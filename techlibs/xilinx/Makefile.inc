
OBJS += techlibs/xilinx/synth_xilinx.o
OBJS += techlibs/xilinx/xilinx_dffopt.o

$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/cells_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/cells_sim.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/cells_xtra.v))

$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/lutrams_xcv.txt))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/lutrams_xcv_map.v))

$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/lutrams_xc5v.txt))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/lutrams_xcu.txt))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/lutrams_xc5v_map.v))

$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/brams_xcv.txt))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/brams_xcv_map.v))

$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/brams_defs.vh))

$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/brams_xc2v.txt))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/brams_xc2v_map.v))

$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/brams_xc3sda.txt))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/brams_xc3sda_map.v))

$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/brams_xc4v.txt))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/brams_xc4v_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/brams_xc5v_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/brams_xc6v_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/brams_xcu_map.v))

$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/urams.txt))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/urams_map.v))

$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/arith_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/ff_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/lut_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/mux_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc3s_mult_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc3sda_dsp_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc6s_dsp_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc4v_dsp_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc5v_dsp_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xc7_dsp_map.v))
$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/xcu_dsp_map.v))

$(eval $(call add_share_file,share/xilinx,techlibs/xilinx/abc9_model.v))

OBJS += techlibs/xilinx/xilinx_dsp.o
GENFILES += techlibs/xilinx/xilinx_dsp_pm.h
GENFILES += techlibs/xilinx/xilinx_dsp48a_pm.h
GENFILES += techlibs/xilinx/xilinx_dsp_CREG_pm.h
GENFILES += techlibs/xilinx/xilinx_dsp_cascade_pm.h
techlibs/xilinx/xilinx_dsp.o: techlibs/xilinx/xilinx_dsp_pm.h techlibs/xilinx/xilinx_dsp48a_pm.h techlibs/xilinx/xilinx_dsp_CREG_pm.h techlibs/xilinx/xilinx_dsp_cascade_pm.h
$(eval $(call add_extra_objs,techlibs/xilinx/xilinx_dsp_pm.h))
$(eval $(call add_extra_objs,techlibs/xilinx/xilinx_dsp48a_pm.h))
$(eval $(call add_extra_objs,techlibs/xilinx/xilinx_dsp_CREG_pm.h))
$(eval $(call add_extra_objs,techlibs/xilinx/xilinx_dsp_cascade_pm.h))

OBJS += techlibs/xilinx/xilinx_srl.o
GENFILES += techlibs/xilinx/xilinx_srl_pm.h
techlibs/xilinx/xilinx_srl.o: techlibs/xilinx/xilinx_srl_pm.h
$(eval $(call add_extra_objs,techlibs/xilinx/xilinx_srl_pm.h))
