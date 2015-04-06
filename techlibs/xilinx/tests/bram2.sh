#!/bin/bash

set -ex
unisims=/opt/Xilinx/Vivado/2014.4/data/verilog/src/unisims
../../../yosys -v2 -l bram2.log -p synth_xilinx -o bram2_syn.v bram2.v
iverilog -T typ -o bram2_tb bram2_tb.v bram2_syn.v -y $unisims $unisims/../glbl.v
vvp -N bram2_tb

