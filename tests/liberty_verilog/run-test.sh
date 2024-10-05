#!/usr/bin/env bash
set -e

for x in *.lib; do
	echo "Testing on $x.."
	echo "read_liberty -lib $x" > test.ys
	echo "write_verilog -blackboxes $x.v.tmp" >> test.ys
	../../yosys -ql ${x%.lib}.log -s test.ys
	sed '1,2d' $x.v.tmp > $x.v
	diff $x.v $x.v.ok
done
