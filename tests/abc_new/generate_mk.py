#!/usr/bin/env python3

import sys
sys.path.append("..")

import glob

import gen_tests_makefile

skip = [
    "duplicate_cell_libs.ys",
    "unknown_cell_zbufs.ys",
]

def create_tests():
    for ys in sorted(glob.glob("*.ys")):
        if ys in skip:
            continue
        gen_tests_makefile.generate_ys_test(ys)

gen_tests_makefile.generate_custom(create_tests)
