#!/bin/bash
set -ex
yosys -p "synth_gowin -top demo -vout demo_syn.v" demo.v
$GOWIN_HOME/bin/gowin -d demo_syn.v -cst demo.cst -sdc demo.sdc -p GW1NR-9-QFN88-6 -pn GW1NR-LV9QN88C6/I5 -cfg device.cfg -bit -tr -ph -timing -gpa -rpt -warning_all

# post place&route simulation (icarus verilog)
if false; then
	iverilog -D POST_IMPL -o testbench -s testbench testbench.v \
			demo_out.v $(yosys-config --datdir/gowin/cells_sim.v)
	vvp -N testbench
fi
