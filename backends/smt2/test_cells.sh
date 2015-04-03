#!/bin/bash

set -ex

rm -rf test_cells
mkdir test_cells
cd test_cells

../../../yosys -p 'test_cell -muxdiv -w test all /$alu /$macc /$fa /$lcu /$lut /$shift /$shiftx'

cat > miter.tpl <<- EOT
; #model# (set-option :produce-models true)
(set-logic QF_UFBV)
%%
(declare-fun s () miter_s)
(assert (|miter_n trigger| s))
(check-sat)
; #model# (get-value ((|miter_n in_A| s) (|miter_n in_B| s) (|miter_n gold_Y| s) (|miter_n gate_Y| s) (|miter_n trigger| s)))
EOT

for x in $(set +x; ls test_*.il | sort -R); do
	x=${x%.il}
	cat > $x.ys <<- EOT
		read_ilang $x.il
		copy gold gate

		cd gate
		techmap; opt; abc;;
		cd ..

		miter -equiv -flatten -make_outputs gold gate miter
		hierarchy -check -top miter

		dump
		write_smt2 -bv -tpl miter.tpl $x.smt2
	EOT
	../../../yosys -q $x.ys
	if ! cvc4 $x.smt2 > $x.result; then
		cat $x.result
		exit 1
	fi
	if ! grep unsat $x.result; then
		echo "Proof failed! Extracting model..."
		sed -i 's/^; #model# //' $x.smt2
		cvc4 $x.smt2
		exit 1
	fi
done

set +x
echo ""
echo "  All tests passed."
echo ""
exit 0

