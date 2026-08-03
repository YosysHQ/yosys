#!/usr/bin/env python3

import sys
sys.path.append("..")

import gen_tests_makefile

gen_tests_makefile.generate_autotest("*.v", "",
"""if grep -Eq 'expect-(wr-ports|rd-ports|rd-clk)' $@; then \\
	$(YOSYS) -f verilog -qp "proc; opt; memory -nomap; dump -outfile $(@:.v=).dmp t:\\$$mem_v2" $@; \\
    python3 validate.py $@  $(@:.v=).dmp; \\
fi""")
