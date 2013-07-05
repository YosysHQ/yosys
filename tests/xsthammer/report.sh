#!/bin/bash

if [ $# -eq 0 ]; then
	echo "Usage: $0 <job_id>" >&2
	exit 1
fi

job="$1"
set --

set -ex
rm -rf report_temp/$job
mkdir -p report report_temp/$job
cd report_temp/$job

cp ../../vivado/$job.v syn_vivado.v
cp ../../quartus/$job.v syn_quartus.v
cp ../../xst/$job.v syn_xst.v
cp ../../rtl/$job.v rtl.v

yosys -p 'hierarchy; proc; opt; techmap; abc; opt' -b 'verilog -noattr' -o syn_yosys.v ../../rtl/$job.v
cat ../../xl_cells.v ../../cy_cells.v > cells.v

{
	echo "module ${job}_test(a, b, y1, y2);"
	sed -r '/^(input|output) / !d; /output/ { s/ y;/ y1;/; p; }; s/ y1;/ y2;/;' rtl.v
	echo "${job}_1 uut1 (.a(a), .b(b), .y(y1));"
	echo "${job}_2 uut2 (.a(a), .b(b), .y(y2));"
	echo "endmodule"
} > test.v

echo -n > fail_patterns.txt
for p in syn_vivado syn_quartus syn_xst syn_yosys rtl; do
for q in syn_vivado syn_quartus syn_xst syn_yosys rtl; do
	if test -f result.${q}.${p}.txt; then
		cp result.${q}.${p}.txt result.${p}.${q}.txt
		continue
	fi

	{
		echo "read_verilog -DGLBL $p.v"
		echo "rename $job ${job}_1"

		echo "read_verilog -DGLBL $q.v"
		echo "rename $job ${job}_2"

		echo "read_verilog cells.v test.v"
		echo "hierarchy -top ${job}_test"
		echo "proc; opt; flatten ${job}_test"
		echo "hierarchy -check -top ${job}_test"

		echo "! touch test.$p.$q.input_ok"
		echo "sat -timeout 10 -verify-no-timeout -show a,b,y1,y2 -prove y1 y2 ${job}_test"
	} > test.$p.$q.ys

	if yosys -l test.$p.$q.log test.$p.$q.ys; then
		if grep TIMEOUT test.$p.$q.log; then
			echo TIMEOUT > result.${p}.${q}.txt
		else
			echo PASS > result.${p}.${q}.txt
		fi
	else
		echo $( grep '^ *\\[ab] ' test.$p.$q.log | gawk '{ print $4; }' | tr -d '\n' ) >> fail_patterns.txt
		echo FAIL > result.${p}.${q}.txt
	fi

	# this fails if an error was encountered before the 'sat' command
	rm test.$p.$q.input_ok
done; done

{
	echo "module testbench;"

	sed -r '/^input / !d; s/^input/reg/;' rtl.v
	for p in syn_vivado syn_quartus syn_xst syn_yosys rtl; do
		sed -r "/^output / !d; s/^output/wire/; s/ y;/ ${p}_y;/;" rtl.v
		echo "${job}_${p} uut_${p} (.a(a), .b(b), .y(${p}_y));"
	done

	echo "initial begin"
	extra_patterns=""
	bits=$( echo $( grep '^input' rtl.v | cut -f2 -d'[' | cut -f1 -d: | tr '\n' '+' )2 | bc; )
	for x in 1 2 3 4 5 6 7 8 9 0; do
		extra_patterns="$extra_patterns $( echo $job$x | sha1sum | gawk "{ print \"160'h\" \$1; }" )"
	done
	for pattern in $bits\'b0 ~$bits\'b0 $( sed "s/^/$bits'b/;" < fail_patterns.txt ) $extra_patterns; do
		echo "  { a, b } <= $pattern; #1;"
		for p in syn_vivado syn_quartus syn_xst syn_yosys rtl; do
			echo "  \$display(\"++RPT++ %b $p\", ${p}_y);"
		done
		echo "  \$display(\"++RPT++ ----\");"
	done
	echo "end"

	echo "endmodule"

	for p in syn_vivado syn_quartus syn_xst syn_yosys rtl; do
		sed "s/^module ${job}/module ${job}_${p}/; /^\`timescale/ d;" < $p.v
	done

	cat cells.v
} > testbench.v

/opt/altera/13.0/modelsim_ase/bin/vlib work
/opt/altera/13.0/modelsim_ase/bin/vlog testbench.v
/opt/altera/13.0/modelsim_ase/bin/vsim -c -do "run; exit" work.testbench | tee sim_modelsim.log

. /opt/Xilinx/14.5/ISE_DS/settings64.sh
vlogcomp testbench.v
fuse -o testbench testbench
{ echo "run all"; echo "exit"; } > run-all.tcl
./testbench -tclbatch run-all.tcl | tee sim_isim.log

for p in syn_vivado syn_quartus syn_xst syn_yosys rtl; do
for q in isim modelsim; do
	echo $( grep '++RPT++' sim_$q.log | sed 's,.*++RPT++ ,,' | grep " $p\$" | gawk '{ print $1; }' | md5sum | gawk '{ print $1; }' ) > result.${p}.${q}.txt
done; done

echo "#00ff00" > color_PASS.txt
echo "#ff0000" > color_FAIL.txt

if cmp result.rtl.isim.txt result.rtl.modelsim.txt; then
	echo "#00ff00" > color_$( cat result.rtl.isim.txt ).txt
else
	echo "#00ff00" > color_NO_SIM_COMMON.txt
fi

{
	echo "<h3>Hammer Report: $job</h3>"
	echo "<table border>"
	echo "<tr><th width=\"100\"></th>"
	for q in syn_vivado syn_quartus syn_xst syn_yosys rtl isim modelsim; do
		echo "<th width=\"100\">$q</th>"
	done
	echo "</tr>"
	for p in syn_vivado syn_quartus syn_xst syn_yosys rtl; do
		echo "<tr><th>$p</th>"
		for q in syn_vivado syn_quartus syn_xst syn_yosys rtl isim modelsim; do
			read result < result.${p}.${q}.txt
			if ! test -f color_$result.txt; then
				case $( ls color_*.txt | wc -l ) in
					3) echo "#ffff00" > color_$result.txt ;;
					4) echo "#ff00ff" > color_$result.txt ;;
					5) echo "#00ffff" > color_$result.txt ;;
					*) echo "#888888" > color_$result.txt ;;
				esac
			fi
			echo "<td align=\"center\" bgcolor=\"$( cat color_$result.txt )\">$( echo $result | cut -c1-8 )</td>"
		done
		echo "</tr>"
	done
	echo "<tr><td colspan=\"8\"><pre>$( perl -pe 's/([<>&])/"&#".ord($1).";"/eg;' rtl.v |
		perl -pe 's!([^\w#]|^)(\w+)\b!$x = $1; $y = $2; sprintf("%s<span style=\"color: %s;\">%s</span>", $x, $y =~ /module|input|wire|output|assign|signed|endmodule/ ? "#008800;" : "#000088;", $y)!eg' )</pre></td></tr>"
	#perl -pe 's,\b(module|input|wire|output|assign|signed|endmodule)\b,<span style="color: #008800;">$1</span>,g' )</pre></td></tr>"
	echo "</table>"
} > ../../report/$job.html

sync
echo READY.

