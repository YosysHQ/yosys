#!/bin/bash

echo "all: all_list" > bram1.mk
all_list="all_list:"

for transp in 0 1; do
for abits in 1 2 4 8 10 16 20; do
for dbits in 1 2 4 8 10 16 20 24 30 32 40 48 50 56 60 64 70 72 80; do
	if [ $(( (1 << $abits) * $dbits )) -gt 1000000 ]; then continue; fi
	if [ $(( (1 << $abits) * $dbits )) -gt 100 ]; then continue; fi
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
		echo "xvlog --work gold bram1_tb.v bram1.v > gold.txt"
		echo "xvlog --work gate bram1_tb.v synth.v > gate.txt"
		echo "xelab -R gold.bram1_tb >> gold.txt"
		# echo "mv testbench.vcd gold.vcd"
		echo "xelab -L unisim -R gate.bram1_tb >> gate.txt"
		# echo "mv testbench.vcd gate.vcd"
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
echo "$all_list" >> bram1.mk

echo "Testing..."
${MAKE:-make} -f bram1.mk
echo

# echo "Cleaning up..."
# rm -rf bram1_cmp bram1.mk bram1_[0-9]*/

