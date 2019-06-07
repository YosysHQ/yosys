#!/bin/bash

set -e
for aig in *.aig; do
    ../../yosys-abc -c "read -c $aig; write ${aig%.*}_ref.v"
    ../../yosys -p "
read_verilog ${aig%.*}_ref.v
prep
design -stash gold
read_aiger -clk_name clock $aig
prep
design -stash gate
design -import gold -as gold
design -import gate -as gate
miter -equiv -flatten -make_assert -make_outputs gold gate miter
sat -verify -prove-asserts -show-ports -seq 16 miter
"
done
