yosys_pass(lattice_gsr
	lattice_gsr.cc
)

yosys_pass(synth_lattice
	synth_lattice.cc
	REQUIRES
		abc
		abc9
		alumacc
		attrmvcp
		autoname
		blackbox
		booth
		check
		clean
		deminout
		dfflegalize
		flatten
		fsm
		hierarchy
		iopadmap
		lattice_gsr
		memory
		memory_libmap
		memory_map
		opt
		opt_clean
		opt_expr
		opt_lut_ins
		opt_merge
		peepopt
		proc
		read_verilog
		share
		simplemap
		stat
		techmap
		tribuf
		wreduce
		write_edif
		write_json
		zinit
	DATA_EXPLICIT
		lattice/cells_ff.vh cells_ff.vh
		lattice/cells_io.vh cells_io.vh
		lattice/cells_map_trellis.v cells_map_trellis.v
		lattice/cells_map_nexus.v cells_map_nexus.v
		lattice/common_sim.vh common_sim.vh
		lattice/parse_init.vh parse_init.vh
		lattice/ccu2d_sim.vh ccu2d_sim.vh
		lattice/ccu2c_sim.vh ccu2c_sim.vh
		lattice/cells_sim_ecp5.v cells_sim_ecp5.v
		lattice/cells_sim_xo2.v cells_sim_xo2.v
		lattice/cells_sim_xo3.v cells_sim_xo3.v
		lattice/cells_sim_xo3d.v cells_sim_xo3d.v
		lattice/cells_sim_nexus.v cells_sim_nexus.v
		lattice/cells_bb_ecp5.v cells_bb_ecp5.v
		lattice/cells_bb_xo2.v cells_bb_xo2.v
		lattice/cells_bb_xo3.v cells_bb_xo3.v
		lattice/cells_bb_xo3d.v cells_bb_xo3d.v
		lattice/cells_bb_nexus.v cells_bb_nexus.v
		lattice/lutrams_map_trellis.v lutrams_map_trellis.v
		lattice/lutrams_trellis.txt lutrams_trellis.txt
		lattice/lutrams_map_nexus.v lutrams_map_nexus.v
		lattice/lutrams_nexus.txt lutrams_nexus.txt
		lattice/lrams_map_nexus.v lrams_map_nexus.v
		lattice/lrams_nexus.txt lrams_nexus.txt
		lattice/brams_map_16kd.v brams_map_16kd.v
		lattice/brams_16kd.txt brams_16kd.txt
		lattice/brams_map_8kc.v brams_map_8kc.v
		lattice/brams_8kc.txt brams_8kc.txt
		lattice/brams_map_nexus.v brams_map_nexus.v
		lattice/brams_nexus.txt brams_nexus.txt
		lattice/arith_map_ccu2c.v arith_map_ccu2c.v
		lattice/arith_map_ccu2d.v arith_map_ccu2d.v
		lattice/arith_map_nexus.v arith_map_nexus.v
		lattice/latches_map.v latches_map.v
		lattice/dsp_map_18x18.v dsp_map_18x18.v
		lattice/dsp_map_nexus.v dsp_map_nexus.v

		ecp5/cells_ff.vh cells_ff.vh
		ecp5/cells_io.vh cells_io.vh
		ecp5/common_sim.vh common_sim.vh
		ecp5/ccu2c_sim.vh ccu2c_sim.vh
		ecp5/cells_sim.v cells_sim_ecp5.v
		ecp5/cells_bb.v cells_bb_ecp5.v

		nexus/parse_init.vh parse_init.vh
		nexus/cells_sim.v cells_sim_nexus.v
		nexus/cells_xtra.v cells_bb_nexus.v
)
