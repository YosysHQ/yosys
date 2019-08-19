#!/bin/bash

set -ex

# Test base testbench
iverilog -DVCDFILE=\"test_arith_no_synth.vcd\" -T typ -o test_arith_no_synth \
    test_arith_tb.v test_arith.v
vvp -N test_arith_no_synth

# Test Xilinx flow
../../../yosys -v2 -l test_arith_xilinx.log -p synth_xilinx \
    -o test_arith_xilinx.v \
    test_arith.v
iverilog -DVCDFILE=\"test_arith_xilinx.vcd\" -T typ -o test_arith_xilinx \
    test_arith_tb.v test_arith_xilinx.v \
    ../cells_sim.v
vvp -N test_arith_xilinx

# Test Xilinx (VPR) flow
../../../yosys -v2 -l test_arith_xilinx_vpr.log -p "synth_xilinx -vpr" \
    -o test_arith_xilinx_vpr.v \
    test_arith.v
iverilog \
    -D_EXPLICIT_CARRY \
    -DVCDFILE=\"test_arith_xilinx_vpr.vcd\" -T typ \
    -o test_arith_xilinx_vpr \
    test_arith_tb.v test_arith_xilinx_vpr.v \
    ../cells_sim.v
vvp -N test_arith_xilinx_vpr
