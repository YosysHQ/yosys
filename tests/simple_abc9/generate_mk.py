#!/usr/bin/env python3

import sys
sys.path.append("..")

import shutil
import os
from pathlib import Path

# ----------------------
# Check if iverilog is installed
# ----------------------
if shutil.which("iverilog") is None:
    print("Error: Icarus Verilog 'iverilog' not found.", file=sys.stderr)
    sys.exit(1)

src_dir = Path("../simple")
# ----------------------
# Copy all files from ../simple to current directory
# ----------------------
for file in src_dir.glob("*.v"):
    shutil.copy(file, os.path.join(".", file.name))

for file in src_dir.glob("*.sv"):
    shutil.copy(file, os.path.join(".", file.name))

# bug 2675
bug_file = os.path.join(".", "specify.v")
if os.path.exists(bug_file):
    os.remove(bug_file)

import gen_tests_makefile

gen_tests_makefile.generate_autotest("*.*v", "-f \"verilog -noblackbox -specify\" -n 300 -p '\
    read_verilog -icells -lib +/abc9_model.v; \
    hierarchy; \
    synth -run coarse; \
    opt -full; \
    techmap; \
    abc9 -lut 4; \
    clean; \
    check -assert * abc9_test037 %d; \
    select -assert-none t:?_NOT_ t:?_AND_ %%; \
    setattr -mod -unset blackbox -unset whitebox =*'")
