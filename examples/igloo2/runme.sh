#!/bin/bash
set -ex
yosys -p 'synth_sf2 -top example -edif netlist.edn -vlog netlist.vm' example.v
LM_LICENSE_FILE=1702@`hostname` /opt/microsemi/Libero_SoC_v11.9/Libero/bin/libero SCRIPT:libero.tcl
