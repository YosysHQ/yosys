#!/bin/bash
set -ex
yosys -p 'synth_sf2 -top example -edif netlist.edn -vlog netlist.vm' example.v
export LM_LICENSE_FILE=${LM_LICENSE_FILE:-1702@localhost}
/opt/microsemi/Libero_SoC_v12.0/Libero/bin/libero SCRIPT:libero.tcl
cp proj/designer/example/export/example.stp .
