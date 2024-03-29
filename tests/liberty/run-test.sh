#!/usr/bin/env bash
set -e

for x in *.lib; do
	echo "Running $x.."
    echo "read_verilog small.v" > test.ys
    echo "synth -top small" >> test.ys
    echo "dfflibmap -info -liberty ${x}" >> test.ys
	../../yosys -ql ${x%.lib}.log -s test.ys
done
