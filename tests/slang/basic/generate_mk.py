#!/usr/bin/env python3

import sys
sys.path.append("..")

import gen_tests_makefile

gen_tests_makefile.generate(["--yosys-scripts", "--bash"],["export ASAN_OPTIONS=halt_on_error=0"])
