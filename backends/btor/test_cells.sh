#!/bin/bash

set -ex

rm -rf test_cells.tmp
mkdir -p test_cells.tmp
cd test_cells.tmp

../../../yosys -p 'test_cell -n 5 -w test all /$alu /$fa /$lcu /$lut /$sop /$macc /$mul /$div /$mod'

for fn in test_*.il; do
	../../../yosys -p "
		read_ilang $fn
		rename gold gate
		synth

		read_ilang $fn
		miter -equiv -make_assert -flatten gold gate main
		hierarchy -top main
		write_btor ${fn%.il}.btor
	"
	boolectormc -kmax 1 --trace-gen --stop-first -v ${fn%.il}.btor > ${fn%.il}.out
	if grep " SATISFIABLE" ${fn%.il}.out; then
		echo "Check failed for ${fn%.il}."
		exit 1
	fi
done

echo "OK."

