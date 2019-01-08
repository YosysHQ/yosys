#!/bin/bash
set -ex
rm -rf work
yosys example.ys
LM_LICENSE_FILE=1702@`hostname` /opt/microsemi/Libero_SoC_v11.9/Libero/bin/libero SCRIPT:libero.tcl
