#!/usr/bin/env bash

set -e

declare -A defines=( ["ice40"]="ICE40_HX ICE40_LP ICE40_U" )

echo "Running syntax check on arch sim models"
for arch in ../../techlibs/*; do
	find $arch -name cells_sim.v | while read path; do
		arch_name=$(basename -- $arch)
		if [ "${defines[$arch_name]}" ]; then
			for def in ${defines[$arch_name]}; do
				echo -n "Test $path -D$def ->"
				iverilog -t null -I$arch -D$def -DNO_ICE40_DEFAULT_ASSIGNMENTS $path
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
