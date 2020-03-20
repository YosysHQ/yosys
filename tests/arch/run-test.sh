#!/bin/bash

set -e

echo "Running syntax check on arch sim models"
for arch in ../../techlibs/*; do
	find $arch -name cells_sim.v | while read path; do
		arch_name=$(basename -- $arch)
		defines=""
		if [ "$arch_name" == "ice40" ]; then
			defines="ICE40_HX ICE40_LP ICE40_U"
		fi
		if [ ! -z "$defines" ]; then
			for def in $defines; do
				echo -n "Test $path -D$def ->"
				iverilog -t null -I$arch -D$def $path
				echo " ok"
			done
		else
			echo -n "Test $path ->"
			iverilog -t null -I$arch $path
			echo " ok"
		fi
	done
done

for path in "../../techlibs/common/simcells.v"  "../../techlibs/common/simlib.v"; do
	echo -n "Test $path ->"
	iverilog -t null $path
	echo " ok"
done
