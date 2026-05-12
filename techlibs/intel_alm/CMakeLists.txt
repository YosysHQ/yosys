yosys_pass(synth_intel_alm
	synth_intel_alm.cc
	REQUIRES
		abc9
		alumacc
		autoname
		blackbox
		check
		clean
		clkbufmap
		deminout
		dfflegalize
		flatten
		fsm
		hierarchy
		iopadmap
		memory
		memory_bram
		memory_map
		opt
		opt_clean
		opt_expr
		peepopt
		proc
		read_verilog
		share
		stat
		techmap
		tribuf
		wreduce
	DATA_DIR
		intel_alm
	DATA_FILES
		# Techmap
		common/abc9_map.v
		common/abc9_unmap.v
		common/abc9_model.v
		common/alm_map.v
		common/alm_sim.v
		common/arith_alm_map.v
		common/dff_map.v
		common/dff_sim.v
		common/dsp_sim.v
		common/dsp_map.v
		common/mem_sim.v
		common/misc_sim.v

		cyclonev/cells_sim.v

		# RAM
		common/bram_m10k.txt
		common/bram_m10k_map.v
		common/lutram_mlab.txt

		# Miscellaneous
		common/megafunction_bb.v
)
