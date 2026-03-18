#!/usr/bin/env python3

import glob
import os
import sys
import argparse

yosys_basedir = os.path.relpath(os.path.join(os.path.dirname(__file__), ".."))
common_mk = os.path.relpath(os.path.join(os.path.dirname(__file__), "common.mk"))

def _cwd_base():
    return os.path.basename(os.getcwd())

def generate_target(name, command, out=sys.stdout):
    #target = f"{_cwd_base()}-{name}"
    target = f"{name}"
    print(f"all: {target}", file=out)
    print(f".PHONY: {target}", file=out)
    print(f"{target}:", file=out)
    if command:
        print(f"\t@$(call run_test,{target}, \\", file=out)
        print(f"\t{command})", file=out)
    else:
        print(f"\t@$(call run_test,{target})", file=out)

def generate_ys_test(ys_file, yosys_args="", commands=""):
    cmd = f'$(YOSYS) -ql {ys_file}.err {yosys_args} {ys_file} >/dev/null 2>&1 && mv {ys_file}.err {ys_file}.log'
    if commands:
        cmd += f"; \\\n{commands}"
    generate_target(ys_file, cmd)

def generate_tcl_test(tcl_file, yosys_args="", commands=""):
    cmd = f'$(YOSYS) -ql {tcl_file}.err {yosys_args} {tcl_file} >/dev/null 2>&1 && mv {tcl_file}.err {tcl_file}.log'
    if commands:
        cmd += f"; \\\n{commands}"
    generate_target(tcl_file, cmd)

def generate_sv_test(sv_file, yosys_args="", commands=""):
    base = os.path.splitext(sv_file)[0]
    if not os.path.exists(base + ".ys"):
        yosys_cmd = '-p "prep -top top; async2sync; sat -enable_undef -verify -prove-asserts"'
        cmd = f'$(YOSYS) -ql {sv_file}.err {yosys_cmd} {yosys_args} {sv_file} >/dev/null 2>&1 && mv {sv_file}.err {sv_file}.log'
        if commands:
            cmd += f"; \\\n{commands}"
        generate_target(sv_file, cmd)

def generate_bash_test(sh_file, commands=""):
    cmd = f"bash -v {sh_file} >{sh_file}.err 2>&1 && mv {sh_file}.err {sh_file}.log"
    if commands:
        cmd += f"; \\\n{commands}"
    generate_target(sh_file, cmd)

def unpack_cmd(cmd):
    if isinstance(cmd, str):
        return cmd
    if isinstance(cmd, (list, tuple)):
        return " \\\n".join(cmd)
    raise TypeError("cmd must be a string or a list/tuple of strings")

def generate_cmd_test(test_name, cmd, yosys_args=""):
    generate_target(test_name, unpack_cmd(cmd))

def generate_tests(argv, cmds):
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument("-y", "--yosys-scripts", action="store_true")
    parser.add_argument("-t", "--tcl-scripts", action="store_true")
    parser.add_argument("-s", "--prove-sv", action="store_true")
    parser.add_argument("-b", "--bash", action="store_true")
    parser.add_argument("-a", "--yosys-args", default="")

    args = parser.parse_args(argv)

    if not (args.yosys_scripts or args.tcl_scripts or args.prove_sv or args.bash):
        raise RuntimeError("No file types selected")

    if args.yosys_scripts:
        for f in sorted(glob.glob("*.ys")):
            generate_ys_test(f, args.yosys_args, cmds)

    if args.tcl_scripts:
        for f in sorted(glob.glob("*.tcl")):
            generate_tcl_test(f, args.yosys_args, cmds)

    if args.prove_sv:
        for f in sorted(glob.glob("*.sv")):
            generate_sv_test(f, args.yosys_args, cmds)

    if args.bash:
        for f in sorted(glob.glob("*.sh")):
            if f != "run-test.sh":
                generate_bash_test(f, cmds)

def print_header(extra=None, out=sys.stdout):
    print(f"include {common_mk}", file=out)
    print(f"YOSYS ?= {yosys_basedir}/yosys", file=out)
    print("", file=out)
    print("export YOSYS_MAX_THREADS := 4", file=out)
    if extra:
        for line in extra:
            print(line, file=out)
    print("", file=out)
    print(".PHONY: all", file=out)
    print("all:", file=out)

def generate(argv, extra=None, cmds=""):
    with open("Makefile", "w") as f:
        old = sys.stdout
        sys.stdout = f
        try:
            print_header(extra)
            generate_tests(argv, cmds)
        finally:
            sys.stdout = old

def generate_custom(callback, extra=None):
    with open("Makefile", "w") as f:
        old = sys.stdout
        sys.stdout = f
        try:
            print_header(extra)
            callback()
        finally:
            sys.stdout = old

def generate_autotest_file(test_file, commands):
    cmd = f"../tools/autotest.sh -G -j ${{SEEDOPT}} ${{EXTRA_FLAGS}} {test_file} >/dev/null 2>&1; \\\n{commands}"
    generate_target(test_file, cmd)

def generate_autotest(pattern, extra_flags, cmds=""):
    with open("Makefile", "w") as f:
        old = sys.stdout
        sys.stdout = f
        try:
            print_header([ f"EXTRA_FLAGS = {extra_flags}",
                           "SEED ?=",
                           "ifneq ($(strip $(SEED)),)",
                           "    SEEDOPT=-S$(SEED)",
                           "endif",
                        ])
            for f in sorted(glob.glob(pattern)):
                generate_autotest_file(f, cmds)
        finally:
            sys.stdout = old
