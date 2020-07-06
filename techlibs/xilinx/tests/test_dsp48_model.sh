#!/bin/bash
set -ex
if [ -z $ISE_DIR ]; then
	ISE_DIR=/opt/Xilinx/ISE/14.7
fi
sed 's/DSP48 /DSP48_UUT /; /DSP48_UUT/,/endmodule/ p; d;' < ../cells_sim.v > test_dsp48_model_uut.v
if [ ! -f "test_dsp48_model_ref.v" ]; then
	cp $ISE_DIR/ISE_DS/ISE/verilog/src/unisims/DSP48.v test_dsp48_model_ref.v
fi
for tb in mult_allreg mult_noreg mult_inreg
do
	iverilog -s $tb -s glbl -o test_dsp48_model test_dsp48_model.v test_dsp48_model_uut.v test_dsp48_model_ref.v $ISE_DIR/ISE_DS/ISE/verilog/src/glbl.v
	vvp -N ./test_dsp48_model
done
