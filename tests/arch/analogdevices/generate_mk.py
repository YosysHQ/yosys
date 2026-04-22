#!/usr/bin/env python3

import sys
sys.path.append("../..")

import gen_tests_makefile
import mem_gen

gen_tests_makefile.generate(["--yosys-scripts", "--bash", "--yosys-args", "-w 'Yosys has only limited support for tri-state logic at the moment.'" ])
