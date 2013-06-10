#!/bin/bash

set -ex
mkdir -p xst
. /opt/Xilinx/14.2/ISE_DS/settings64.sh

rm -rf xst_temp
mkdir xst_temp
cd xst_temp

if [ $# -eq 0 ]; then
	set -- $( ls ../rtl | sed 's,\.v$,,' )
fi

for job
do
	cat > $job.xst <<- EOT
		run
		-ifn $job.prj
		-ifmt mixed
		-ofn $job
		-ofmt NGC
		-p xc6vlx75t-2-ff784
		-top $job
		-opt_mode Speed
		-opt_level 1
		-power NO
		-iuc NO
		-keep_hierarchy NO
		-rtlview Yes
		-glob_opt AllClockNets
		-read_cores YES
		-write_timing_constraints NO
		-cross_clock_analysis NO
		-hierarchy_separator /
		-bus_delimiter <>
		-case maintain
		-slice_utilization_ratio 100
		-bram_utilization_ratio 100
		-dsp_utilization_ratio 100
		-fsm_extract YES -fsm_encoding Auto
		-safe_implementation No
		-fsm_style lut
		-ram_extract Yes
		-ram_style Auto
		-rom_extract Yes
		-shreg_extract YES
		-rom_style Auto
		-auto_bram_packing NO
		-resource_sharing YES
		-async_to_sync NO
		-use_dsp48 auto
		-iobuf NO
		-max_fanout 100000
		-bufg 32
		-register_duplication YES
		-register_balancing No
		-optimize_primitives NO
		-use_clock_enable Auto
		-use_sync_set Auto
		-use_sync_reset Auto
		-iob auto
		-equivalent_register_removal YES
		-slice_utilization_ratio_maxmargin 5
	EOT

	cat > $job.prj <<- EOT
		verilog work "../rtl/$job.v"
	EOT

	xst -ifn $job.xst
	netgen -w -ofmt verilog $job.ngc $job
	cp $job.v ../xst/$job.v
done

