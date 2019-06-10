#!/bin/bash

set -e

# NB: *.aag and *.aig must contain a symbol table naming the primary
#     inputs and outputs, otherwise ABC and Yosys will name them
#     arbitrarily (and inconsistently with each other).

for aag in *.aag; do
    # Since ABC cannot read *.aag, read the *.aig instead
    # (which would have been created by the reference aig2aig utility,
    #  available from http://fmv.jku.at/aiger/)
    ../../yosys-abc -c "read -c ${aag%.*}.aig; write ${aag%.*}_ref.v"
    ../../yosys -p "
read_verilog ${aag%.*}_ref.v
prep
design -stash gold
read_aiger -clk_name clock $aag
prep
design -stash gate
design -import gold -as gold
design -import gate -as gate
miter -equiv -flatten -make_assert -make_outputs gold gate miter
sat -verify -prove-asserts -show-ports -seq 16 miter
"
done

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
