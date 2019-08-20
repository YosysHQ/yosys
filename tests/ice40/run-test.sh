#!/bin/bash
set -e
if [ -f "../../../../../techlibs/common/simcells.v" ]; then
	COMMON_PREFIX=../../../../../techlibs/common
	TECHLIBS_PREFIX=../../../../../techlibs
else
	COMMON_PREFIX=/usr/local/share/yosys
	TECHLIBS_PREFIX=/usr/local/share/yosys
fi
for x in *_top.v; do
  echo "Running $x.."
  ../../yosys -q -s ${x%_top.v}.ys -l ./temp/${x%.v}.log $x
  echo "Simulating $x.."
  iverilog -o ./temp/${x%_top.v}_testbench  ${x%_top.v}_tb.v ./temp/${x%_top.v}_synth.v common.v $COMMON_PREFIX/simcells.v $TECHLIBS_PREFIX/ice40/cells_sim.v
  if ! vvp -N ./temp/${x%_top.v}_testbench > ./temp/${x%_top.v}_testbench.log 2>&1; then
		grep 'ERROR' ./temp/${x%_top.v}_testbench.log
		exit 0
	elif grep 'ERROR' ./temp/${x%_top.v}_testbench.log || ! grep 'OKAY' ./temp/${x%_top.v}_testbench.log; then
		exit 0
  fi
done
