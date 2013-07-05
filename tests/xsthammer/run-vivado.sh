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

sed 's/^module/(* use_dsp48="no" *) module/;' < ../../rtl/$job.v > rtl.v
cat > $job.tcl <<- EOT
	read_verilog rtl.v
	synth_design -part xc7k70t -top $job
	write_verilog -force ../../vivado/$job.v
EOT

/opt/Xilinx/Vivado/2013.2/bin/vivado -mode batch -source $job.tcl

sync
exit 0

