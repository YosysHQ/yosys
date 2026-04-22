#!/usr/bin/env python3

import sys
sys.path.append("..")

import gen_tests_makefile
import glob

def create_tests():
    yss = sorted(glob.glob("*.ys"))
    for ys in yss:
        gen_tests_makefile.generate_ys_test(ys)

    cmd = [ "python3 frontend.py unix-socket frontend.sock" ]
    gen_tests_makefile.generate_cmd_test("frontend.py", cmd)

gen_tests_makefile.generate_custom(create_tests)
