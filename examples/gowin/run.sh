#!/bin/bash
set -ex
yosys -p "synth_gowin -top demo -vout demo_syn.v" demo.v
$GOWIN_HOME/bin/gowin -d demo_syn.v -cst demo.cst -sdc demo.sdc -p GW2A55-PBGA484-6 \
		-warning_all -out demo_out.v -rpt demo.rpt -tr demo_tr.html -bit demo.bit

# post place&route simulation (icarus verilog)
if false; then
	iverilog -D POST_IMPL -o testbench -s testbench testbench.v \
			demo_out.v $(yosys-config --datdir/gowin/cells_sim.v)
	vvp -N testbench
fi
