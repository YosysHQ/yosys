#!/usr/bin/env python3

import sys
sys.path.append("..")

import gen_tests_makefile

gen_tests_makefile.generate(["--yosys-scripts"], [],
"""[ ! -f $(@:.ys=.blif) ] || \\
    diff <(tail -n +2 $(@:.ys=.blif).out) <(tail -n +2 $(@:.ys=.blif).ok) >/dev/null 2>&1 || exit 1; \\
""")