#!/bin/bash

# iverlog simulation
echo "Doing Verilog simulation with iverilog"
iverilog -o dsn counter.v counter_tb.v 
./dsn -lxt2
gtkwave counter_tb.vcd &

# yosys synthesis
set -ex

../../yosys counter_digital.ys

# requires ngspice with xspice support enabled:
ngspice testbench_digital.sp
