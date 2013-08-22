#!/bin/bash

set -ex

XILINX_DIR=/opt/Xilinx/14.5/ISE_DS/ISE/

../../yosys - <<- EOT
	# read design
	read_verilog counter.v

	# high-level synthesis
	hierarchy -check -top counter
	proc; opt; fsm; opt; techmap; opt

	# mapping logic to LUTs using Berkeley ABC
	abc -lut 6; opt

	# map internal cells to FPGA cells
	techmap -map cells.v; opt

	# write netlist
	write_verilog -noattr testbench_synth.v
EOT

iverilog -o testbench_gold counter_tb.v counter.v
iverilog -o testbench_gate counter_tb.v testbench_synth.v \
	$XILINX_DIR/verilog/src/{glbl,unisims/{FDRE,LUT1,LUT2,LUT3,LUT4,LUT5,LUT6}}.v

./testbench_gold > testbench_gold.txt
./testbench_gate > testbench_gate.txt

if diff -u testbench_gold.txt testbench_gate.txt; then
	set +x; echo; echo; banner "  PASS  "
else
	exit 1
fi

if [ "$*" = "-clean" ]; then
	rm -f testbench_{synth.v,{gold,gate}{,.txt}}
fi

