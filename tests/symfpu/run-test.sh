#!/usr/bin/env bash
set -eu

source ../gen-tests-makefile.sh

# operators
ops="sqrt add sub mul div muladd"
for op in $ops; do
    rm -f ${op}_edges.*
done

prove_op() {
    op=$1
    defs=$2
    ys_file=${op}_edges.ys
    echo """\
symfpu -op $op
sat -prove-asserts -verify
chformal -remove
opt

read_verilog -sv -formal $defs edges.sv
chformal -lower
prep -top edges -flatten
sat -prove-asserts -verify
""" > $ys_file
}

prove_op sqrt "-DSQRT"
prove_op add "-DADD -DADDSUB -DADDS"
prove_op sub "-DSUB -DADDSUB -DADDS"
prove_op mul "-DMUL -DMULS"
prove_op div "-DDIV"
prove_op muladd "-DMULADD -DMULS -DADDS"

# rounding modes
rms="RNE RNA RTP RTN RTZ"
for rm in $rms; do
    rm -f ${rm}_edges.*
done

prove_rm() {
    rm=$1
    defs=$2
    ys_file=${rm}_edges.ys
    echo """\
symfpu -rm $rm
sat -prove-asserts -verify
chformal -remove
opt

read_verilog -sv -formal $defs edges.sv
chformal -lower
prep -top edges -flatten
sat -prove-asserts -verify
""" > $ys_file
}

prove_rm RNE "-DRNE"
prove_rm RNA "-DRNA"
prove_rm RTP "-DRTP"
prove_rm RTN "-DRTN"
prove_rm RTZ "-DRTZ"

generate_mk --yosys-scripts
