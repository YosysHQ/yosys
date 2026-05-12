pmgen_command(test_pmgen
	test_pmgen.pmg
)
yosys_test_pass(pmgen
	test_pmgen.cc
	${PMGEN_test_pmgen_OUTPUT}
	REQUIRES
		synth_ice40
		synth_xilinx
)
# Test implementation directly depends on generated files from these passes.
add_dependencies(yosys_test_pmgen
	yosys_ice40_dsp
	yosys_xilinx_srl
)
