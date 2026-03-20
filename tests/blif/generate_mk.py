#!/usr/bin/env python3

import sys
sys.path.append("..")

import gen_tests_makefile

gen_tests_makefile.generate(["--yosys-scripts"], [],
"""[ ! -f $(@:.ys=.blif) ] || \\
    sed '1d' $(@:.ys=.blif).out | diff - <(sed '1d' $(@:.ys=.blif).ok) >/dev/null 2>&1 || exit 1; \\
""")