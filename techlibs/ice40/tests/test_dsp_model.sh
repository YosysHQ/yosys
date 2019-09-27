#!/bin/bash
set -ex
sed 's/SB_MAC16/SB_MAC16_UUT/; /SB_MAC16_UUT/,/endmodule/ p; d;' < ../cells_sim.v > test_dsp_model_uut.v
if [ ! -f "test_dsp_model_ref.v" ]; then
	cat /opt/lscc/iCEcube2.2017.01/verilog/sb_ice_syn.v > test_dsp_model_ref.v
fi
for tb in testbench \
		testbench_comb_8x8_A testbench_comb_8x8_B testbench_comb_16x16 \
		testbench_seq_16x16_A testbench_seq_16x16_B \
		testbench_comb_8x8_A_signedA testbench_comb_8x8_A_signedB testbench_comb_8x8_A_signedAB \
		testbench_comb_8x8_B_signedA testbench_comb_8x8_B_signedB testbench_comb_8x8_B_signedAB \
		testbench_comb_16x16_signedA testbench_comb_16x16_signedB testbench_comb_16x16_signedAB
do
	iverilog -s $tb -o test_dsp_model test_dsp_model.v test_dsp_model_uut.v test_dsp_model_ref.v
	vvp -N ./test_dsp_model
done
