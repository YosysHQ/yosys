#!/usr/bin/env python3

import sys
sys.path.append("..")

import shutil

# ----------------------
# Check if iverilog is installed
# ----------------------
if shutil.which("iverilog") is None:
    print("Error: Icarus Verilog 'iverilog' not found.", file=sys.stderr)
    sys.exit(1)

import gen_tests_makefile

gen_tests_makefile.generate_autotest("*.v", "",
"""if grep -Eq 'expect-(wr-ports|rd-ports|rd-clk)' $@; then \\
	$(YOSYS) -f verilog -qp "proc; opt; memory -nomap; dump -readable -outfile $(@:.v=).dmp t:\\$$mem_v2" $@; \\
    python3 validate.py $@  $(@:.v=).dmp; \\
fi""")
