#!/bin/bash

if [ $# -eq 0 ]; then
	echo "Usage: $0 <job_id>" >&2
	exit 1
fi

job="$1"
set --

set -e
mkdir -p check check_temp
cd check_temp

{
	echo "module ${job}_top(a, b, y_rtl, y_xst);"
	sed -r '/^(input|output) / !d; /output/ { s/ y;/ y_rtl;/; p; }; s/ y_rtl;/ y_xst;/;' ../rtl/$job.v
	echo "${job}_rtl rtl_variant (.a(a), .b(b), .y(y_rtl));"
	echo "${job}_xst xst_variant (.a(a), .b(b), .y(y_xst));"
	echo "endmodule"
} > ${job}_top.v

for mode in nomap techmap; do
	{
		echo "read_verilog -DGLBL ../xst/$job.v"
		echo "rename $job ${job}_xst"

		echo "read_verilog ../rtl/$job.v"
		echo "rename $job ${job}_rtl"
		if [ $mode = techmap ]; then
			echo "techmap ${job}_rtl"
		fi

		echo "read_verilog ${job}_top.v"
		echo "read_verilog ../xl_cells.v"

		echo "hierarchy -top ${job}_top"
		echo "flatten ${job}_top"
		echo "hierarchy -top ${job}_top"
		echo "opt_clean"

		echo "rename ${job}_top ${job}_top_${mode}"
		echo "write_ilang ${job}_top_${mode}.il"
	} > ${job}_top_${mode}.ys
	../../../yosys -q ${job}_top_${mode}.ys
done

{
	echo "read_ilang ${job}_top_nomap.il"
	echo "read_ilang ${job}_top_techmap.il"
	echo "sat -verify -show a,b,y_rtl,y_xst -prove y_rtl y_xst ${job}_top_nomap"
	echo "sat -verify -show a,b,y_rtl,y_xst -prove y_rtl y_xst ${job}_top_techmap"
} > ${job}_cmp.ys

if ../../../yosys -l ${job}.log ${job}_cmp.ys; then
	mv ${job}.log ../check/${job}.log
	rm -f ../check/${job}.err
else
	mv ${job}.log ../check/${job}.err
	rm -f ../check/${job}.log
	exit 1
fi

exit 0

