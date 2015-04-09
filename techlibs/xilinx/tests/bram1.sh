#!/bin/bash

set -e

transp_list="0 1"
abits_list="1 2 4 8 10 16 20"
dbits_list="1 2 4 8 10 16 20 24 30 32 40 48 50 56 60 64 70 72 80"

use_xsim=false
unisims=/opt/Xilinx/Vivado/2014.4/data/verilog/src/unisims

echo "all: all_list" > bram1.mk
all_list=""

for transp in $transp_list; do
for abits in $abits_list; do
for dbits in $dbits_list; do
	if [ $(( (1 << $abits) * $dbits )) -gt 1000000 ]; then continue; fi
	id=`printf "%d%02d%02d" $transp $abits $dbits`
	echo "Creating bram1_$id.."
	rm -rf bram1_$id
	mkdir -p bram1_$id
	cp bram1.v bram1_tb.v bram1_$id/
	sed -i "/parameter/ s,ABITS *= *[0-9]*,ABITS = $abits," bram1_$id/*.v
	sed -i "/parameter/ s,DBITS *= *[0-9]*,DBITS = $dbits," bram1_$id/*.v
	sed -i "/parameter/ s,TRANSP *= *[0-9]*,TRANSP = $transp," bram1_$id/*.v
	{
		echo "set -e"
		echo "../../../../yosys -q -lsynth.log -p 'synth_xilinx -top bram1; write_verilog synth.v' bram1.v"
		if $use_xsim; then
			echo "xvlog --work gold bram1_tb.v bram1.v > gold.txt"
			echo "xvlog --work gate bram1_tb.v synth.v > gate.txt"
			echo "xelab -R gold.bram1_tb >> gold.txt"
			echo "xelab -L unisim -R gate.bram1_tb >> gate.txt"
		else
			echo "iverilog -o bram1_tb_gold bram1_tb.v bram1.v > gold.txt 2>&1"
			echo "iverilog -o bram1_tb_gate bram1_tb.v synth.v -y $unisims $unisims/../glbl.v > gate.txt 2>&1"
			echo "./bram1_tb_gold >> gold.txt"
			echo "./bram1_tb_gate >> gate.txt"
		fi
		echo "../bram1_cmp <( grep '#OUT#' gold.txt; ) <( grep '#OUT#' gate.txt; )"
	} > bram1_$id/run.sh
	{
		echo "bram1_$id/ok:"
		echo "	@cd bram1_$id && bash run.sh"
		echo "	@echo -n '[$id]'"
		echo "	@touch \$@"
	} >> bram1.mk
	all_list="$all_list bram1_$id/ok"
done; done; done

cc -o bram1_cmp ../../../tests/tools/cmp_tbdata.c
echo all_list: $(echo $all_list | tr ' ' '\n' | sort -R) >> bram1.mk

echo "Testing..."
${MAKE:-make} -f bram1.mk
echo

echo "Used bram types:"
grep -h 'Mapping to bram type' bram1_*/synth.log | sort | uniq -c

echo "Cleaning up..."
rm -rf bram1_cmp bram1.mk bram1_[0-9]*/

