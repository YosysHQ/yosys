#!/bin/bash

set -e

echo "Running syntax check on arch sim models"
for arch in ../../techlibs/*; do
	find $arch -name cells_sim.v | while read path; do
		echo -n "Test $path ->"
		iverilog -t null -I$arch $path
		echo " ok"
	done
done

for path in "../../techlibs/common/simcells.v"  "../../techlibs/common/simlib.v"; do
	echo -n "Test $path ->"
	iverilog -t null $path
	echo " ok"
done
