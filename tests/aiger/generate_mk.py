#!/usr/bin/env python3

import sys
sys.path.append("..")

import gen_tests_makefile

import glob
import os

def base(fn):
    return os.path.splitext(fn)[0]

# NB: *.aag and *.aig must contain a symbol table naming the primary
#     inputs and outputs, otherwise ABC and Yosys will name them
#     arbitrarily (and inconsistently with each other).

# Since ABC cannot read *.aag, read the *.aig instead
# (which would have been created by the reference aig2aig utility,
#  available from http://fmv.jku.at/aiger/)
def create_tests():
    aags = sorted(glob.glob("*.aag"))
    yss = sorted(glob.glob("*.ys"))
    for aag in aags:
        b = base(aag)

        cmd = [
            f"$(ABC) -q \"read -c {b}.aig; write {b}_ref.v\" >/dev/null 2>&1;",
            "$(YOSYS) -qp \"",
            f"read_verilog {b}_ref.v;",
            "prep;",
            "design -stash gold;",
            f"read_aiger -clk_name clock {aag};",
            "prep;",
            "design -stash gate;",
            "design -import gold -as gold;",
            "design -import gate -as gate;",
            "miter -equiv -flatten -make_assert -make_outputs gold gate miter;",
            "sat -verify -prove-asserts -show-ports -seq 16 miter;",
            f"\" -l {aag}.log >/dev/null 2>&1"
        ]

        gen_tests_makefile.generate_cmd_test(aag, cmd)

    # ---- Yosys script tests ----
    for ys in yss:
        gen_tests_makefile.generate_ys_test(ys)

    cmd = [ "rm -rf gate; mkdir gate;",
            "$(YOSYS) --no-version -p \"test_cell -aigmap -w gate/ -n 1 -s 1 all\" >/dev/null 2>&1;",
            "set -o pipefail; diff --brief gold gate | tee aigmap.err;",
            "rm -f aigmap.err" ]

    gen_tests_makefile.generate_cmd_test("aigmap", cmd)

extra = [ f"ABC ?= {gen_tests_makefile.yosys_basedir}/yosys-abc" ]

gen_tests_makefile.generate_custom(create_tests, extra)
