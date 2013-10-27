#!/bin/bash

set -ex

XILINX_DIR=/opt/Xilinx/14.5/ISE_DS/ISE
XILINX_PART=xc6slx9-2-tqg144

../../../yosys - <<- EOT
	read_verilog example.v
	synth_xilinx -edif synth.edif
EOT

$XILINX_DIR/bin/lin64/edif2ngd -a synth.edif synth.ngo
$XILINX_DIR/bin/lin64/ngdbuild -p $XILINX_PART -uc example.ucf synth.ngo synth.ngd
$XILINX_DIR/bin/lin64/map -p $XILINX_PART -w -o mapped.ncd synth.ngd constraints.pcf
$XILINX_DIR/bin/lin64/par -w mapped.ncd placed.ncd constraints.pcf
$XILINX_DIR/bin/lin64/bitgen -w placed.ncd example.bit constraints.pcf

