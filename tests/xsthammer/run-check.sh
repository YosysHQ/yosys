#!/bin/bash

use_vivado=false
checkdir="check"

if [ "$1" = "-vivado" ]; then
	use_vivado=true
	checkdir="check_vivado"
	shift
fi

if [ $# -eq 0 ]; then
	echo "Usage: $0 <job_id>" >&2
	exit 1
fi

job="$1"
set --

set -e
mkdir -p $checkdir check_temp/$job
cd check_temp/$job

{
	echo "module ${job}_top(a, b, y_rtl, y_xst);"
	sed -r '/^(input|output) / !d; /output/ { s/ y;/ y_rtl;/; p; }; s/ y_rtl;/ y_xst;/;' ../../rtl/$job.v
	echo "${job}_rtl rtl_variant (.a(a), .b(b), .y(y_rtl));"
	echo "${job}_xst xst_variant (.a(a), .b(b), .y(y_xst));"
	echo "endmodule"
} > ${job}_top.v

for mode in nomap techmap; do
	{
		if $use_vivado; then
			echo "read_verilog ../../vivado/$job.v"
		else
			echo "read_verilog -DGLBL ../../xst/$job.v"
		fi
		echo "rename $job ${job}_xst"

		echo "read_verilog ../../rtl/$job.v"
		echo "rename $job ${job}_rtl"
		if [ $mode = techmap ]; then
			echo "techmap ${job}_rtl"
		fi

		echo "read_verilog ${job}_top.v"
		echo "read_verilog ../../xl_cells.v"

		echo "hierarchy -top ${job}_top"
		echo "flatten ${job}_xst"
		echo "flatten ${job}_rtl"
		echo "flatten ${job}_top"
		echo "opt_clean"

		echo "rename ${job}_xst ${job}_xst_${mode}"
		echo "rename ${job}_rtl ${job}_rtl_${mode}"
		echo "rename ${job}_top ${job}_top_${mode}"
		echo "dump -outfile ${job}_top_${mode}.il ${job}_xst_${mode} ${job}_rtl_${mode} ${job}_top_${mode}"
	} > ${job}_top_${mode}.ys
	../../../../yosys -q ${job}_top_${mode}.ys
done

{
	echo "read_ilang ${job}_top_nomap.il"
	echo "read_ilang ${job}_top_techmap.il"
	echo "sat -timeout 60 -verify-no-timeout -show a,b,y_rtl,y_xst -prove y_rtl y_xst ${job}_top_nomap"
	echo "sat -timeout 60 -verify-no-timeout -show a,b,y_rtl,y_xst -prove y_rtl y_xst ${job}_top_techmap"
	if [[ $job != expression_* ]]; then
		echo "eval -brute_force_equiv_checker ${job}_rtl_nomap   ${job}_xst_nomap"
		echo "eval -brute_force_equiv_checker ${job}_rtl_techmap ${job}_xst_techmap"
	fi
} > ${job}_cmp.ys

if ../../../../yosys -l ${job}.log ${job}_cmp.ys; then
	mv ${job}.log ../../$checkdir/${job}.log
	rm -f ../../$checkdir/${job}.err
else
	mv ${job}.log ../../$checkdir/${job}.err
	rm -f ../../$checkdir/${job}.log
	exit 1
fi

exit 0

