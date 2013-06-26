#!/bin/bash

if [ $# -eq 0 ]; then
	echo "Usage: $0 <job_id>" >&2
	exit 1
fi

job="$1"
set --

set -e
mkdir -p vivado vivado_temp/$job
cd vivado_temp/$job

cat > $job.tcl <<- EOT
	read_verilog ../../rtl/$job.v
	synth_design -part xc7k70t -top $job
	write_verilog ../../vivado/$job.v
EOT

. /opt/Xilinx/14.5/ISE_DS/settings64.sh

vivado -mode batch -source $job.tcl

exit 0

