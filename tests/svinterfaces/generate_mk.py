#!/usr/bin/env python3

from pathlib import Path
import glob
import sys
sys.path.append("..")

import gen_tests_makefile

runone_tests = [
    "svinterface1",
    #"svinterface_at_top"
]

def run_one():
    for testname in runone_tests:
        cmd_lines = [
            f'$(YOSYS) -p "read_verilog -sv {testname}.sv ; hierarchy -check -top TopModule ; synth ; write_verilog {testname}_syn.v" >> {testname}.log_stdout 2>> {testname}.log_stderr',
            f'$(YOSYS) -p "read_verilog -sv {testname}_ref.v ; hierarchy -check -top TopModule ; synth ; write_verilog {testname}_ref_syn.v" >> {testname}.log_stdout 2>> {testname}.log_stderr',
            f'rm -f a.out reference_result.txt dut_result.txt',
            f'iverilog -g2012 {testname}_syn.v',
            f'iverilog -g2012 {testname}_ref_syn.v',
            f'iverilog -g2012 {testname}_tb.v {testname}_ref_syn.v',
            f'./a.out',
            f'mv output.txt reference_result.txt',
            f'iverilog -g2012 {testname}_tb_wrapper.v {testname}_syn.v' if testname=="svinterface_at_top" else
            f'iverilog -g2012 {testname}_tb.v {testname}_syn.v',
            f'./a.out',
            f'mv output.txt dut_result.txt',
            f'diff reference_result.txt dut_result.txt > {testname}.diff',
        ]
        gen_tests_makefile.generate_cmd_test(testname, cmd_lines)

def run_simple():
    for f in sorted(glob.glob("*.ys")):
        gen_tests_makefile.generate_ys_test(f)

def main():
    def callback():
        run_one()
        run_simple()

    gen_tests_makefile.generate_custom(callback)

if __name__ == "__main__":
    main()
