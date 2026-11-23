yosys_pass(xilinx_dffopt
	xilinx_dffopt.cc
)
yosys_pass(xilinx_dsp
	xilinx_dsp.cc
	xilinx_dsp.h
	xilinx_dsp48a.h
	xilinx_dsp_CREG.h
	xilinx_dsp_cascade.h
)
yosys_pass(xilinx_srl
	xilinx_srl.cc
	xilinx_srl.h
)

yosys_pass(synth_xilinx
	synth_xilinx.cc
	REQUIRES
		abc
		alumacc
		blackbox
		check
		chtype
		clean
		clkbufmap
		deminout
		dfflegalize
		extractinv
		flatten
		fsm
		hierarchy
		iopadmap
		memory
		memory_dff
		memory_libmap
		memory_map
		muxcover
		muxpack
		opt
		opt_clean
		opt_expr
		opt_lut_ins
		peepopt
		pmux2shiftx
		proc
		read_verilog
		select
		setattr
		share
		simplemap
		sort
		stat
		synth
		techmap
		tribuf
		wreduce
		write_blif
		write_edif
		write_json
		xilinx_dffopt
		xilinx_dsp
		xilinx_srl
		zinit
	DATA_DIR
		xilinx
	DATA_FILES
		cells_map.v
		cells_sim.v
		cells_xtra.v

		lutrams_xcv.txt
		lutrams_xcv_map.v

		lutrams_xc5v.txt
		lutrams_xcu.txt
		lutrams_xc5v_map.v

		brams_xcv.txt
		brams_xcv_map.v

		brams_defs.vh

		brams_xc2v.txt
		brams_xc2v_map.v

		brams_xc3sda.txt
		brams_xc3sda_map.v

		brams_xc4v.txt
		brams_xc4v_map.v
		brams_xc5v_map.v
		brams_xc6v_map.v
		brams_xcu_map.v

		urams.txt
		urams_map.v

		arith_map.v
		ff_map.v
		lut_map.v
		mux_map.v
		xc3s_mult_map.v
		xc3sda_dsp_map.v
		xc6s_dsp_map.v
		xc4v_dsp_map.v
		xc5v_dsp_map.v
		xc7_dsp_map.v
		xcu_dsp_map.v

		abc9_model.v
)
