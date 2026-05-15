#!/usr/bin/env python3

import sys
sys.path.append("..")

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
