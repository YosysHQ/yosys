#!/usr/bin/env python3

import glob

import sys
sys.path.append("..")

import gen_tests_makefile

def generate_write_test(sv_file: str):
    # if the first line of the file starts with // (ie a comment), the rest of
    # the line is treated as the commands to run after reading the input
    header_cmds = ""
    with open(sv_file, "r") as f:
        line = f.readline().rstrip()
        if line.startswith("//"):
            header_cmds = line[3:]

    # process input & write output
    read_cmd = f"read -sv {sv_file}; {header_cmds}"
    out_file = f"{sv_file}.out"
    out_yosys_cmd = f"{read_cmd}; rename gold gate; write_verilog {out_file}"
    out_cmd = f'$(YOSYS) -l {out_file}.err -p "{out_yosys_cmd}" && mv {out_file}.err {out_file}.log'
    gen_tests_makefile.generate_target(out_file, out_cmd)

    # test input & output equivalence
    equiv = "equiv_make gold gate equiv; equiv_induct equiv; equiv_status -assert equiv"
    yosys_cmd = f"{read_cmd}; design -stash gold; read -sv {out_file}; {header_cmds}; design -import gold; {equiv}"
    cmd = f'$(YOSYS) -l {sv_file}.err -p "{yosys_cmd}" && mv {sv_file}.err {sv_file}.log'
    gen_tests_makefile.generate_target(sv_file, cmd, [out_file])

def generate_write_tests():
    # currently configured to use `read -sv` on each
    for f in sorted(glob.glob("*.sv")):
        generate_write_test(f)

gen_tests_makefile.generate_custom(generate_write_tests)
