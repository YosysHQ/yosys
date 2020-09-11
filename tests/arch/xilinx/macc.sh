../../../yosys -qp "synth_xilinx -top macc2; rename -top macc2_uut" -o macc_uut.v macc.v
iverilog -o test_macc macc_tb.v macc_uut.v macc.v ../../../techlibs/xilinx/cells_sim.v
vvp -N ./test_macc
../../../yosys -qp "synth_xilinx -family xc6s -top macc2; rename -top macc2_uut" -o macc_uut.v macc.v
iverilog -o test_macc macc_tb.v macc_uut.v macc.v ../../../techlibs/xilinx/cells_sim.v
vvp -N ./test_macc
