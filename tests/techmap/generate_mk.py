#!/usr/bin/env python3

import sys
sys.path.append("..")

import gen_tests_makefile

gen_tests_makefile.generate(["--yosys-scripts", "--tcl-scripts", "--bash", "--yosys-args", "-e 'select out of bounds'"])
