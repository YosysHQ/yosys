#!/usr/bin/env bash
set -eo pipefail

for x in *.lib; do
	echo "Testing on $x.."
	../../yosys -p "read_verilog small.v; synth -top small; dfflibmap -info -liberty ${x}" -ql ${x%.lib}.log
	../../yosys-filterlib - $x 2>/dev/null > $x.filtered
	../../yosys-filterlib -verilogsim $x > $x.verilogsim
	diff $x.filtered $x.filtered.ok
	diff $x.verilogsim $x.verilogsim.ok
	if [[ -e ${x%.lib}.log.ok ]]; then
		../../yosys -p "dfflibmap -info -liberty ${x}" -TqqQl ${x%.lib}.log
		diff ${x%.lib}.log ${x%.lib}.log.ok
	fi
done

for x in *.ys; do
  echo "Running $x.."
  ../../yosys -q -s $x -l ${x%.ys}.log
done

