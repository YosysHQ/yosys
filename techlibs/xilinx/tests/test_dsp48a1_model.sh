#!/bin/bash
set -ex
if [ -z $ISE_DIR ]; then
	ISE_DIR=/opt/Xilinx/ISE/14.7
fi
sed 's/DSP48A1/MARKER1/; s/DSP48A/DSP48A_UUT/; s/MARKER1/DSP48A1_UUT/; /module DSP48A_UUT/,/endmodule/ p; /module DSP48A1_UUT/,/endmodule/ p; d;' < ../cells_sim.v > test_dsp48a1_model_uut.v
if [ ! -f "test_dsp48a1_model_ref.v" ]; then
	cp $ISE_DIR/ISE_DS/ISE/verilog/src/unisims/DSP48A1.v test_dsp48a1_model_ref.v
fi
if [ ! -f "test_dsp48a_model_ref.v" ]; then
	cp $ISE_DIR/ISE_DS/ISE/verilog/src/unisims/DSP48A.v test_dsp48a_model_ref.v
fi
for tb in mult_allreg mult_noreg mult_inreg
do
	iverilog -s $tb -s glbl -o test_dsp48a1_model test_dsp48a1_model.v test_dsp48a1_model_uut.v test_dsp48a1_model_ref.v test_dsp48a_model_ref.v $ISE_DIR/ISE_DS/ISE/verilog/src/glbl.v
	vvp -N ./test_dsp48a1_model
done
