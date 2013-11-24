#!/bin/bash

set -ex

XILINX_DIR=/opt/Xilinx/14.5/ISE_DS/ISE

../../../yosys -p 'synth_xilinx -top counter; write_verilog -noattr testbench_synth.v' counter.v

iverilog -o testbench_gold counter_tb.v counter.v
iverilog -o testbench_gate counter_tb.v testbench_synth.v \
	$XILINX_DIR/verilog/src/{glbl,unisims/{FDRE,LUT1,LUT2,LUT3,LUT4,LUT5,LUT6,BUFGP,IBUF}}.v

./testbench_gold > testbench_gold.txt
./testbench_gate > testbench_gate.txt

if diff -u testbench_gold.txt testbench_gate.txt; then
	set +x; echo; echo; banner "  PASS  "
else
	exit 1
fi

rm -f testbench_{synth,gold,gate,mapped}*

