#!/bin/bash

set -ex

yosys_bin="/usr/local/synthesis/src/yosys/yosys"
iverilog_bin="iverilog"

all_modes="yosys hana vis icarus odin"
all_sources="always01 always02 always03 arrays01 forgen01 forgen02"

gcc -o cmp_tbdata cmp_tbdata.c

for src in $all_sources; do
	echo; echo
	$yosys_bin -o ${src}_tb.v -b autotest ${src}.v
	$iverilog_bin -o ${src}_tb ${src}_tb.v ${src}.v
	./${src}_tb > ${src}_tb.out
        for mode in $all_modes; do
		simlib=""
		[ -f ${src}_${mode}.v ] || continue
		[ -f simlib_${mode}.v ] && simlib="simlib_${mode}.v"
		if $iverilog_bin -o ${src}_${mode}_tb -s testbench ${src}_tb.v ${src}_${mode}.v $simlib; then
			./${src}_${mode}_tb > ${src}_${mode}_tb.out
		else
			rm -f ${src}_${mode}_tb.out
		fi
        done
done

set +x
echo; echo; echo

{
	for mode in $all_modes; do
		echo -en "\t$mode"
	done; echo

	for src in $all_sources; do
		echo -n "$src"
		for mode in $all_modes; do
			if [ -f ${src}_${mode}.v ]; then
				if [ ! -s ${src}_${mode}_tb.out ]; then
					echo -en "\tmissing"
				elif ./cmp_tbdata ${src}_tb.out ${src}_${mode}_tb.out; then
					echo -en "\tok"
				else
					echo -en "\tfailed"
				fi
			else
				echo -en "\terror"
			fi
		done; echo
	done
} | expand -t12

