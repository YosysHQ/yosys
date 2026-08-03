yosys_pass(gatemate_foldinv
	gatemate_foldinv.cc
)

add_custom_command(
	DEPENDS make_lut_tree_lib.py
	# yosys_pass(DATA_FILES) expects the files to be in the source directory
	OUTPUT ${CMAKE_CURRENT_SOURCE_DIR}/lut_tree_cells.genlib ${CMAKE_CURRENT_SOURCE_DIR}/lut_tree_map.v
	COMMAND ${Python3_EXECUTABLE} make_lut_tree_lib.py
	WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
	VERBATIM
)
yosys_pass(synth_gatemate
	synth_gatemate.cc
	REQUIRES
		abc
		alumacc
		blackbox
		check
		clean
		clkbufmap
		deminout
		dfflegalize
		flatten
		fsm
		gatemate_foldinv
		hierarchy
		iopadmap
		memory
		memory_libmap
		memory_map
		muxcover
		muxpack
		opt
		opt_clean
		opt_expr
		peepopt
		proc
		read_verilog
		share
		simplemap
		stat
		techmap
		tribuf
		wreduce
		write_json
		write_verilog
	DATA_DIR
		gatemate
	DATA_FILES
		reg_map.v
		mux_map.v
		lut_map.v
		mul_map.v
		arith_map.v
		cells_sim.v
		cells_bb.v
		brams_map.v
		brams.txt
		brams_init_20.vh
		brams_init_40.vh
		inv_map.v
		lut_tree_cells.genlib
		lut_tree_map.v
)
