#!/bin/bash
set -ex
if [ -z $VIVADO_DIR ]; then
	VIVADO_DIR=/opt/Xilinx/Vivado/2019.1
fi
sed 's/DSP48E1/DSP48E1_UUT/; /DSP48E1_UUT/,/endmodule/ p; d;' < ../cells_sim.v > test_dsp_model_uut.v
if [ ! -f "test_dsp_model_ref.v" ]; then
	cp $VIVADO_DIR/data/verilog/src/unisims/DSP48E1.v test_dsp_model_ref.v
fi
for tb in macc_overflow_underflow \
	simd24_preadd_noreg_nocasc simd12_preadd_noreg_nocasc \
	 mult_allreg_nopreadd_nocasc mult_noreg_nopreadd_nocasc  \
	mult_allreg_preadd_nocasc mult_noreg_preadd_nocasc mult_inreg_preadd_nocasc
do
	iverilog -s $tb -s glbl -o test_dsp_model test_dsp_model.v test_dsp_model_uut.v test_dsp_model_ref.v $VIVADO_DIR/data/verilog/src/glbl.v
	vvp -N ./test_dsp_model
done
