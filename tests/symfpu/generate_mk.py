#!/usr/bin/env python3

import sys
sys.path.append("..")
import gen_tests_makefile

from pathlib import Path
from textwrap import dedent

cwd = Path.cwd()
for path in cwd.glob("*_edges.*"):
    path.unlink()

for op, defs in {
    # standard ops
    "sqrt": "-DSQRT -DSQRTS",
    "add": "-DADD -DADDSUB -DADDS",
    "sub": "-DSUB -DADDSUB -DADDS",
    "mul": "-DMUL -DMULS",
    "div": "-DDIV -DDIVS",
    "muladd": "-DMULADD -DMULS -DADDS",
    # altops
    "altdiv": "-DALTDIV -DDIVS",
    "altsqrt": "-DALTSQRT -DSQRTS",
    # unrounded
    "min": "-DMIN -DCOMPARES",
    "max": "-DMAX -DCOMPARES",
}.items():
    rms = ["DYN"]
    dyn_only = op in ["min", "max"]
    if not dyn_only:
        rms.extend(["RNE", "RNA", "RTP", "RTN", "RTZ"])
    for rm in rms:
        with open(f"{op}_{rm}_edges.ys", "w") as ys:
            print(f"symfpu -op {op} -rm {rm}", file=ys)
            if rm != "DYN" or dyn_only:
                print("sat -prove-asserts -verify", file=ys)
            print(
                dedent(f"""\
                    chformal -remove
                    opt

                    read_verilog -sv -formal {defs} -D{rm} edges.sv
                    chformal -remove -cover
                    chformal -lower
                    prep -top edges -flatten
                    sat -set-assumes -prove-asserts -verify"""
                ), file=ys)

gen_tests_makefile.generate(["--yosys-scripts"])
