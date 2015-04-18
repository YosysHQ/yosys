#!/bin/bash
set -ex
for CLKPOL in 0 1; do
for ENABLE_EN in 0 1; do
for RESET_EN in 0 1; do
for RESET_VAL in 0 1; do
for RESET_SYN in 0 1; do
	pf="test_ffs_${CLKPOL}${ENABLE_EN}${RESET_EN}${RESET_VAL}${RESET_SYN}"
	sed -e "s/CLKPOL = 0/CLKPOL = ${CLKPOL}/;" -e "s/ENABLE_EN = 0/ENABLE_EN = ${ENABLE_EN}/;" \
	    -e "s/RESET_EN = 0/RESET_EN = ${RESET_EN}/;" -e "s/RESET_VAL = 0/RESET_VAL = ${RESET_VAL}/;" \
	    -e "s/RESET_SYN = 0/RESET_SYN = ${RESET_SYN}/;" test_ffs.v > ${pf}_gold.v
	../../../yosys -o ${pf}_gate.v -p "synth_ice40" ${pf}_gold.v
	../../../yosys -p "proc; opt; test_autotb ${pf}_tb.v" ${pf}_gold.v
	iverilog -s testbench -o ${pf}_gold ${pf}_gold.v ${pf}_tb.v
	iverilog -s testbench -o ${pf}_gate ${pf}_gate.v ${pf}_tb.v ../cells_sim.v
	./${pf}_gold > ${pf}_gold.txt
	./${pf}_gate > ${pf}_gate.txt
	cmp ${pf}_gold.txt ${pf}_gate.txt
done; done; done; done; done
echo OK.
