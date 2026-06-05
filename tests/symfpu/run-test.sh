#!/usr/bin/env bash
set -eu

source ../gen-tests-makefile.sh

rm -f *_edges.*

prove_rm() {
    op=$1
    rm=$2
    defs=$3
    ys_file=${op}_${rm}_edges.ys
    echo "symfpu -op $op -rm $rm" > $ys_file
    if [[ $rm != "DYN" ]] then
        echo "sat -prove-asserts -verify" >> $ys_file
    fi
    echo """\
chformal -remove
opt

read_verilog -sv -formal $defs -D${rm} edges.sv
chformal -remove -cover
chformal -lower
prep -top edges -flatten
sat -set-assumes -prove-asserts -verify
""" >> $ys_file
}

prove_op() {
    op=$1
    defs=$2
    rms="RNE RNA RTP RTN RTZ DYN"
    for rm in $rms; do
        prove_rm $op $rm "$defs"
    done
}

prove_op_unrounded() {
    # DYN is default rounding mode, so this is (currently) equivalent to no rounding mode
    # but this does skip verifying the built in asserts
    op=$1
    defs=$2
    prove_rm $op "DYN" "$defs"
}

prove_op sqrt "-DSQRT -DSQRTS"
prove_op add "-DADD -DADDSUB -DADDS"
prove_op sub "-DSUB -DADDSUB -DADDS"
prove_op mul "-DMUL -DMULS"
prove_op div "-DDIV -DDIVS"
prove_op muladd "-DMULADD -DMULS -DADDS"

prove_op altdiv "-DALTDIV -DDIVS"
prove_op altsqrt "-DALTSQRT -DSQRTS"

prove_op_unrounded min "-DMIN -DCOMPARES"
prove_op_unrounded max "-DMAX -DCOMPARES"

generate_mk --yosys-scripts
