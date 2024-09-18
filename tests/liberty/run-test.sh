#!/usr/bin/env bash
set -e

for x in *.lib; do
	echo "Testing on $x.."
	../../yosys -p "read_verilog small.v; synth -top small; dfflibmap -info -liberty ${x}" -ql ${x%.lib}.log
	../../yosys-filterlib - $x 2>/dev/null > $x.filtered
	../../yosys-filterlib -verilogsim $x > $x.verilogsim
	diff $x.filtered $x.filtered.ok && diff $x.verilogsim $x.verilogsim.ok
done

for x in *.ys; do
  echo "Running $x.."
  ../../yosys -q -s $x -l ${x%.ys}.log
done
