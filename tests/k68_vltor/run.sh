#!/bin/bash

if (
	set -ex
	cd verilog-sim-benchmarks
	rm -rf obj_dir_* synth

	cd rtl
	mkdir -p ../synth
	../../../../yosys -o ../synth/k68_soc.v -p 'hierarchy -check -top k68_soc; proc; opt; memory; opt' \
			k68_soc.v k68_arb.v k68_cpu.v k68_load.v k68_clkgen.v k68_decode.v k68_execute.v \
			k68_fetch.v k68_regbank.v k68_buni.v k68_b2d.v k68_ccc.v k68_d2b.v k68_rox.v \
			k68_calc.v k68_dpmem.v k68_sasc.v sasc_brg.v sasc_top.v sasc_fifo4.v

	cd ..
	VERILATOR_OPT="-Wno-fatal -Ibench --cc bench/k68_soc_test.v --exe bench/bench.cpp -prefix m68 -x-assign 0"
	verilator -Mdir obj_dir_rtl -Irtl $VERILATOR_OPT; make -C obj_dir_rtl -f m68.mk
	verilator -Mdir obj_dir_synth -Isynth $VERILATOR_OPT; make -C obj_dir_synth -f m68.mk

	./obj_dir_rtl/m68 100000 | tee output_rtl.txt
	./obj_dir_synth/m68 100000 | tee output_synth.txt
	diff -u <( grep ' sum ' output_rtl.txt; ) <( grep ' sum ' output_synth.txt; )
); then
	echo OK
	exit 0
else
	echo ERROR
	exit 1
fi

