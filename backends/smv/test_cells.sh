#!/bin/bash

set -ex

rm -rf test_cells.tmp
mkdir -p test_cells.tmp
cd test_cells.tmp

# don't test $mul to reduce runtime
# don't test $div and $mod to reduce runtime and avoid "div by zero" message
../../../yosys -p 'test_cell -n 5 -w test all /$alu /$fa /$lcu /$lut /$macc /$mul /$div /$mod'

cat > template.txt << "EOT"
%module main
  INVARSPEC ! bool(_trigger);
EOT

for fn in test_*.il; do
	../../../yosys -p "
		read_ilang $fn
		rename gold gate
		synth

		read_ilang $fn
		miter -equiv -flatten gold gate main
		hierarchy -top main
		write_smv -tpl template.txt ${fn#.il}.smv
	"
	nuXmv -dynamic ${fn#.il}.smv > ${fn#.il}.out
done

grep '^-- invariant .* is false' *.out || echo 'All OK.'

