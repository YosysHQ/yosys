#!/bin/bash
set -ex
sed 's/SB_MAC16/SB_MAC16_UUT/; /SB_MAC16_UUT/,/endmodule/ p; d;' < ../cells_sim.v > test_dsp_model_uut.v
cat /opt/lscc/iCEcube2.2017.01/verilog/sb_ice_syn.v > test_dsp_model_ref.v
iverilog -s testbench -o test_dsp_model test_dsp_model.v test_dsp_model_uut.v test_dsp_model_ref.v
./test_dsp_model
