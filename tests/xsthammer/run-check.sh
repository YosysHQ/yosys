#!/bin/bash

use_vivado=false
use_quartus=false
checkdir="check"

if [ "$1" = "-vivado" ]; then
	use_vivado=true
	checkdir="check_vivado"
	shift
fi

if [ "$1" = "-quartus" ]; then
	use_quartus=true
	checkdir="check_quartus"
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
	echo "module ${job}_top(a, b, y_rtl, y_syn);"
	sed -r '/^(input|output) / !d; /output/ { s/ y;/ y_rtl;/; p; }; s/ y_rtl;/ y_syn;/;' ../../rtl/$job.v
	echo "${job}_rtl rtl_variant (.a(a), .b(b), .y(y_rtl));"
	echo "${job}_syn syn_variant (.a(a), .b(b), .y(y_syn));"
	echo "endmodule"
} > ${job}_top.v

for mode in nomap techmap; do
	{
		if $use_quartus; then
			echo "read_verilog ../../quartus/$job.v"
		elif $use_vivado; then
			echo "read_verilog ../../vivado/$job.v"
		else
			echo "read_verilog -DGLBL ../../xst/$job.v"
		fi
		echo "rename $job ${job}_syn"

		echo "read_verilog ../../rtl/$job.v"
		echo "rename $job ${job}_rtl"
		if [ $mode = techmap ]; then
			echo "techmap ${job}_rtl"
		fi

		echo "read_verilog ${job}_top.v"
		if $use_quartus; then
			echo "read_verilog ../../cy_cells.v"
		else
			echo "read_verilog ../../xl_cells.v"
		fi

		echo "hierarchy -top ${job}_top"
		echo "proc"

		echo "flatten ${job}_syn"
		echo "flatten ${job}_rtl"
		echo "flatten ${job}_top"
		echo "opt_clean"

		echo "rename ${job}_syn ${job}_syn_${mode}"
		echo "rename ${job}_rtl ${job}_rtl_${mode}"
		echo "rename ${job}_top ${job}_top_${mode}"
		echo "dump -outfile ${job}_top_${mode}.il ${job}_syn_${mode} ${job}_rtl_${mode} ${job}_top_${mode}"
	} > ${job}_top_${mode}.ys
	../../../../yosys -q ${job}_top_${mode}.ys
done

{
	echo "read_ilang ${job}_top_nomap.il"
	echo "read_ilang ${job}_top_techmap.il"
	echo "sat -timeout 60 -verify-no-timeout -show a,b,y_rtl,y_syn -prove y_rtl y_syn ${job}_top_nomap"
	echo "sat -timeout 60 -verify-no-timeout -show a,b,y_rtl,y_syn -prove y_rtl y_syn ${job}_top_techmap"
	if [[ $job != expression_* ]]; then
		echo "eval -brute_force_equiv_checker ${job}_rtl_nomap   ${job}_syn_nomap"
		echo "eval -brute_force_equiv_checker ${job}_rtl_techmap ${job}_syn_techmap"
	fi
} > ${job}_cmp.ys

if ../../../../yosys -l ${job}.log ${job}_cmp.ys; then
	mv ${job}.log ../../$checkdir/${job}.log
	rm -f ../../$checkdir/${job}.err
	touch ../../$checkdir/${job}.log
else
	mv ${job}.log ../../$checkdir/${job}.err
	rm -f ../../$checkdir/${job}.log
fi

exit 0

