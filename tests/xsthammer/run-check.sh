#!/bin/bash

set -ex
mkdir -p check

rm -rf check_temp
mkdir check_temp
cd check_temp

for job in $( ls ../rtl | sed 's,\.v$,,' )
do
	{
		echo "module top(a, b, y1, y2);"
		sed -r '/^(input|output) / !d; /output/ { s/ y;/ y1;/; p; }; s/ y1;/ y2;/;' ../rtl/$job.v
		echo "${job}_rtl rtl_variant (.a(a), .b(b), .y(y1));"
		echo "${job}_xst xst_variant (.a(a), .b(b), .y(y1));"
		echo "endmodule"
	} > ${job}_top.v

	{
		echo "read_verilog -DGLBL ../xst/$job.v"
		echo "rename $job ${job}_xst"

		echo "read_verilog ../rtl/$job.v"
		echo "rename $job ${job}_rtl"

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
		echo "sat -verify -prove y1 y2 top"
	} > ${job}_cmp.ys

	yosys ${job}_top.ys
	if yosys -l ${job}.log ${job}_cmp.ys; then
		mv ${job}.log ../check/${job}.log
	else
		mv ${job}.log ../check/${job}.err
	fi

	break;
done

