#!/bin/bash

if [ $# -eq 0 ]; then
	echo "Usage: $0 <job_id>" >&2
	exit 1
fi

job="$1"
set --

set -e
mkdir -p xst xst_temp/$job
cd xst_temp/$job

cat > $job.xst <<- EOT
	run
	-ifn $job.prj -ofn $job -p artix7 -top $job
	-iobuf NO -ram_extract NO -rom_extract NO -use_dsp48 NO
	-fsm_extract YES -fsm_encoding Auto
EOT

cat > $job.prj <<- EOT
	verilog work "../../rtl/$job.v"
EOT

. /opt/Xilinx/14.5/ISE_DS/settings64.sh

xst -ifn $job.xst
netgen -w -ofmt verilog $job.ngc $job
cp $job.v ../../xst/$job.v

sync
exit 0

