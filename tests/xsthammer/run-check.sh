#!/bin/bash

set -ex
mkdir -p check

rm -rf check_temp
mkdir check_temp
cd check_temp

if [ $# -eq 0 ]; then
	set -- $( ls ../rtl | sed 's,\.v$,,' )
fi

for job
do
	{
		echo "module top(a, b, y_rtl, y_xst);"
		sed -r '/^(input|output) / !d; /output/ { s/ y;/ y_rtl;/; p; }; s/ y_rtl;/ y_xst;/;' ../rtl/$job.v
		echo "${job}_rtl rtl_variant (.a(a), .b(b), .y(y_rtl));"
		echo "${job}_xst xst_variant (.a(a), .b(b), .y(y_xst));"
		echo "endmodule"
	} > ${job}_top.v

	{
		echo "read_verilog -DGLBL ../xst/$job.v"
		echo "rename $job ${job}_xst"

		echo "read_verilog ../rtl/$job.v"
		echo "rename $job ${job}_rtl"
		# echo "techmap ${job}_rtl"

		echo "read_verilog ${job}_top.v"
		echo "read_verilog ../xl_cells.v"

		echo "hierarchy -top top"
		echo "flatten top"
		echo "hierarchy -top top"
		echo "opt_clean"

		echo "write_ilang ${job}_top.il"
	} > ${job}_top.ys

	{
		echo "read_ilang ${job}_top.il"
		echo "sat -verify -show a,b,y_rtl,y_xst -prove y_rtl y_xst top"
	} > ${job}_cmp.ys

	../../../yosys ${job}_top.ys

	if ../../../yosys -l ${job}.log ${job}_cmp.ys; then
		mv ${job}.log ../check/${job}.log
		rm -f ../check/${job}.err
	else
		mv ${job}.log ../check/${job}.err
		rm -f ../check/${job}.log
		# break
	fi
done

