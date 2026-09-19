#!/usr/bin/env python3

import sys
sys.path.append("..")

import glob

import gen_tests_makefile

skip = [
    "hier_check.ys",
    "keep_wire.ys",
]

def create_tests():
    for ys in sorted(glob.glob("*.ys")):
        if ys in skip:
            continue
        gen_tests_makefile.generate_ys_test(ys)

gen_tests_makefile.generate_custom(create_tests)
