#!/usr/bin/env python3

import sys
sys.path.append("..")

import gen_tests_makefile

def callback():
    gen_tests_makefile.generate_cmd_test("functional",f'pytest -v -m "not smt and not rkt" . "$$@"')

gen_tests_makefile.generate_custom(callback)
