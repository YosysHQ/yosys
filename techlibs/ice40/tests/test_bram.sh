#!/bin/bash

set -ex

for abits in 7 8 9 10 11 12; do
for dbits in 2 4 8 16 24 32; do
	id="test_bram_${abits}_${dbits}"
	sed -e "s/ABITS = ./ABITS = $abits/g; s/DBITS = ./DBITS = $dbits/g;" < test_bram.v > ${id}.v
	sed -e "s/ABITS = ./ABITS = $abits/g; s/DBITS = ./DBITS = $dbits/g;" < test_bram_tb.v > ${id}_tb.v
	../../../yosys -ql ${id}_syn.log -p "synth_ice40" -o ${id}_syn.v ${id}.v
	# iverilog -s bram_tb -o ${id}_tb ${id}_syn.v ${id}_tb.v /opt/lscc/iCEcube2.2014.08/verilog/sb_ice_syn.v
	iverilog -s bram_tb -o ${id}_tb ${id}_syn.v ${id}_tb.v ../cells_sim.v
	./${id}_tb > ${id}_tb.txt
	if grep -H ERROR ${id}_tb.txt; then false; fi
done; done
echo OK

