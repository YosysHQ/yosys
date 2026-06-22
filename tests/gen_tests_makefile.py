#!/usr/bin/env python3

import glob
import os
import sys
import argparse
from contextlib import contextmanager

yosys_basedir = os.path.relpath(os.path.join(os.path.dirname(__file__), ".."))
common_mk = os.path.relpath(os.path.join(os.path.dirname(__file__), "common.mk"))

# When SKIP_BROKEN_TESTS is set, tests listed (one "<dir>/<file>" per line,
# relative to tests/, '#' comments allowed) in broken_tests.txt are not emitted
# into the generated Makefiles, so `make SKIP_BROKEN_TESTS=1` runs only the
# known-good tests. Regenerate the list with ./regen_broken_tests.sh.
_tests_dir = os.path.dirname(os.path.abspath(__file__))
_broken_tests = set()
if os.environ.get("SKIP_BROKEN_TESTS"):
    _bt_path = os.path.join(_tests_dir, "broken_tests.txt")
    if os.path.exists(_bt_path):
        with open(_bt_path) as _bt_f:
            for _line in _bt_f:
                _line = _line.split("#", 1)[0].strip()
                if _line:
                    _broken_tests.add(os.path.normpath(_line))

def _cwd_base():
    return os.path.basename(os.getcwd())

def _is_broken(name):
    if not _broken_tests:
        return False
    key = os.path.normpath(os.path.join(os.path.relpath(os.getcwd(), _tests_dir), name))
    return key in _broken_tests

def generate_target(name, command, deps = None):
    #target = f"{_cwd_base()}-{name}"
    target = f"{name}"
    if _is_broken(name):
        print(f"# skipped via broken_tests.txt: {name}")
        return
    print(f"all: {target}")
    print(f".PHONY: {target}")
    print(f"{target}_cmd={command}")
    if deps:
        print(f"{target}: {' '.join(deps)}")
    else:
        print(f"{target}:")

    print(f"\t@$(call run_test,{target}, $({target}_cmd))")

def generate_ys_test(ys_file, yosys_args="", commands=""):
    cmd = f'$(YOSYS) -ql {ys_file}.err {yosys_args} {ys_file} && mv {ys_file}.err {ys_file}.log'
    if commands:
        cmd += f"; \\\n{commands}"
    generate_target(ys_file, cmd)

def generate_tcl_test(tcl_file, yosys_args="", commands=""):
    cmd = f'$(YOSYS) -ql {tcl_file}.err {yosys_args} {tcl_file} && mv {tcl_file}.err {tcl_file}.log'
    if commands:
        cmd += f"; \\\n{commands}"
    generate_target(tcl_file, cmd)

def generate_sv_test(sv_file, yosys_args="", commands=""):
    base = os.path.splitext(sv_file)[0]
    if not os.path.exists(base + ".ys"):
        yosys_cmd = '-p "prep -top top; async2sync; sat -enable_undef -verify -prove-asserts"'
        cmd = f'$(YOSYS) -ql {sv_file}.err {yosys_cmd} {yosys_args} {sv_file} && mv {sv_file}.err {sv_file}.log'
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
        return " && \\\n".join(cmd)
    raise TypeError("cmd must be a string or a list/tuple of strings")

def generate_cmd_test(test_name, cmd, yosys_args="", deps = None):
    generate_target(test_name, unpack_cmd(cmd), deps)

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

def print_header(extra=None):
    print(f"include {common_mk}")
    if extra:
        for line in extra:
            print(line)
    print("")
    print(".PHONY: all")
    print("all:")

@contextmanager
def redirect_stdout(new_target):
    old_target, sys.stdout = sys.stdout, new_target
    try:
        yield new_target
    finally:
        sys.stdout = old_target

def generate(argv, extra=None, cmds=""):
    with open("Makefile", "w") as f:
        with redirect_stdout(f):
            print_header(extra)
            generate_tests(argv, cmds)

def generate_custom(callback, extra=None):
    with open("Makefile", "w") as f:
        with redirect_stdout(f):
            print_header(extra)
            callback()

def generate_autotest_file(test_file, commands):
    cmd = f"../tools/autotest.sh -G -j ${{SEEDOPT}} -Y ${{YOSYS}} ${{EXTRA_FLAGS}} {test_file}; \\\n{commands}"
    generate_target(test_file, cmd)

def generate_autotest(pattern, extra_flags, cmds=""):
    with open("Makefile", "w") as f:
        with redirect_stdout(f):
            print_header([ f"EXTRA_FLAGS = {extra_flags}",
                           "SEED ?=",
                           "ifneq ($(strip $(SEED)),)",
                           "    SEEDOPT=-S$(SEED)",
                           "endif",
                        ])
            for fn in sorted(glob.glob(pattern)):
                generate_autotest_file(fn, cmds)
