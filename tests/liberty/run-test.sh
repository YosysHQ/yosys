#!/usr/bin/env bash
set -e

for x in *.lib; do
	echo "Testing on $x.."
	echo "read_verilog small.v" > test.ys
	echo "synth -top small" >> test.ys
	echo "dfflibmap -info -liberty ${x}" >> test.ys
	../../yosys -ql ${x%.lib}.log -s test.ys
	../../yosys-filterlib - $x 2>/dev/null > $x.filtered
	../../yosys-filterlib -verilogsim $x > $x.verilogsim
	diff $x.filtered $x.filtered.ok && diff $x.verilogsim $x.verilogsim.ok
done
