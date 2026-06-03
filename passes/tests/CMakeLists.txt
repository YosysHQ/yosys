yosys_test_pass(autotb
	test_autotb.cc
)
yosys_test_pass(cell
	test_cell.cc
)
yosys_test_pass(abcloop
	test_abcloop.cc
)

yosys_pass(raise_error
	raise_error.cc
)
