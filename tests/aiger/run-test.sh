#!/usr/bin/env bash
source ../common-env.sh

set -e

OPTIND=1
abcprog="../../yosys-abc"    # default to built-in version of abc
while getopts "A:" opt
do
    case "$opt" in
	A) abcprog="$OPTARG" ;;
    esac
done
shift "$((OPTIND-1))"

# NB: *.aag and *.aig must contain a symbol table naming the primary
#     inputs and outputs, otherwise ABC and Yosys will name them
#     arbitrarily (and inconsistently with each other).

for aag in *.aag; do
    # Since ABC cannot read *.aag, read the *.aig instead
    # (which would have been created by the reference aig2aig utility,
    #  available from http://fmv.jku.at/aiger/)
    echo "Checking $aag."
    $abcprog -q "read -c ${aag%.*}.aig; write ${aag%.*}_ref.v"
    ../../yosys -qp "
read_verilog ${aag%.*}_ref.v
prep
design -stash gold
read_aiger -clk_name clock $aag
prep
design -stash gate
design -import gold -as gold
design -import gate -as gate
formalff -clk2ff
miter -equiv -flatten -make_assert -make_outputs gold gate miter
sat -verify -prove-asserts -show-ports -seq 16 miter
" -l ${aag}.log
done

for aig in *.aig; do
    echo "Checking $aig."
    $abcprog -q "read -c $aig; write ${aig%.*}_ref.v"
    ../../yosys -qp "
read_verilog ${aig%.*}_ref.v
prep
design -stash gold
read_aiger -clk_name clock $aig
prep
design -stash gate
design -import gold -as gold
design -import gate -as gate
formalff -clk2ff
miter -equiv -flatten -make_assert -make_outputs gold gate miter
sat -verify -prove-asserts -show-ports -seq 16 miter
" -l ${aig}.log
done

for y in *.ys; do
    echo "Running $y."
    ../../yosys -ql ${y%.*}.log $y
done

# compare aigmap with reference
# make gold with: rm gold/*; yosys --no-version -p "test_cell -aigmap -w gold/ -n 1 -s 1 all"
rm -rf gate; mkdir gate
../../yosys --no-version -p "test_cell -aigmap -w gate/ -n 1 -s 1 all"
(
    set -o pipefail
    diff --brief gold gate | tee aigmap.err
)
rm aigmap.err
