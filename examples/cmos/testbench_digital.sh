#!/bin/bash

set -ex

# iverlog simulation
echo "Doing Verilog simulation with iverilog"
iverilog -o counter_tb counter.v counter_tb.v 
./counter_tb; gtkwave counter_tb.gtkw &

# yosys synthesis
../../yosys counter_digital.ys

# requires ngspice with xspice support enabled:
ngspice testbench_digital.sp

