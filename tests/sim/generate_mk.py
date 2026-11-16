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

# ----------------------
# Check if vcd2fst is installed
# ----------------------
if shutil.which("vcd2fst") is None:
    print("Error: GTKWave tool 'vcd2fst' not found.", file=sys.stderr)
    sys.exit(1)

import gen_tests_makefile

import subprocess
from pathlib import Path

print("Generate FST for sim models")

for name in Path("tb").rglob("tb*.v"):
    test_name = name.stem
    print(f"Test {test_name}")

    verilog_name = f"{test_name[3:]}.v"

    out_file = Path("tb") / f"{test_name}.out"

    subprocess.run(
        ["iverilog", "-o", str(out_file), str(name), verilog_name],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        check=True
    )

    subprocess.run(
        [str(out_file), "-fst"],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
        check=True
    )

gen_tests_makefile.generate(["--yosys-scripts", "--bash", "--yosys-args", "-w 'Yosys has only limited support for tri-state logic at the moment.'" ])
