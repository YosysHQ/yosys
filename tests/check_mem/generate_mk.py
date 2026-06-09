#!/usr/bin/env python3

import sys
sys.path.append("..")

import gen_tests_makefile

gen_tests_makefile.generate(["--check-sv", "--yosys-scripts"], yosys_cmds="hierarchy; proc; check_mem -assert")
