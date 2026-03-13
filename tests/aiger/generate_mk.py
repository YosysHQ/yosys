#!/usr/bin/env python3

import glob
import os

yosys = "../../yosys"
default_abc = "../../yosys-abc"

aags = sorted(glob.glob("*.aag"))
yss = sorted(glob.glob("*.ys"))

print("ABC ?= " + default_abc)
print("YOSYS ?= " + yosys)
print()

def base(fn):
    return os.path.splitext(fn)[0]

# NB: *.aag and *.aig must contain a symbol table naming the primary
#     inputs and outputs, otherwise ABC and Yosys will name them
#     arbitrarily (and inconsistently with each other).

# Since ABC cannot read *.aag, read the *.aig instead
# (which would have been created by the reference aig2aig utility,
#  available from http://fmv.jku.at/aiger/)

for aag in aags:
    b = base(aag)

    print(f"all: {aag}")
    print(f".PHONY: {aag}")
    print(f"{aag}:")
    print(f"\t@echo Checking {aag}.")
    print(f"\t@$(ABC) -q \"read -c {b}.aig; write {b}_ref.v\" >/dev/null 2>&1")
    print("\t@$(YOSYS) -qp \"\\")
    print(f"\tread_verilog {b}_ref.v; \\")
    print("\tprep; \\")
    print("\tdesign -stash gold; \\")
    print(f"\tread_aiger -clk_name clock {aag}; \\")
    print("\tprep; \\")
    print("\tdesign -stash gate; \\")
    print("\tdesign -import gold -as gold; \\")
    print("\tdesign -import gate -as gate; \\")
    print("\tmiter -equiv -flatten -make_assert -make_outputs gold gate miter; \\")
    print("\tsat -verify -prove-asserts -show-ports -seq 16 miter; \\")
    print(f"\t\" -l {aag}.log >/dev/null 2>&1")
    print()

# ---- Yosys script tests ----
for ys in yss:
    b = base(ys)
    print(f"all: {ys}")
    print(f".PHONY: {ys}")
    print(f"{ys}: ")
    print(f"\t@echo Running {ys}.")
    print(f"\t@$(YOSYS) -ql {b}.log {ys} >/dev/null 2>&1")
    print()

# ---- aigmap test ----
print(f"all: aigmap")
print(f".PHONY: aigmap")
print("aigmap:")
print("\t@echo Running aigmap.")
print("\t@rm -rf gate; mkdir gate")
print('\t@$(YOSYS) --no-version -p "test_cell -aigmap -w gate/ -n 1 -s 1 all" >/dev/null 2>&1')
print("\t@set -o pipefail; diff --brief gold gate | tee aigmap.err")
print("\t@rm -f aigmap.err")
print()
