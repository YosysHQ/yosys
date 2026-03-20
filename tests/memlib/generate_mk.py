#!/usr/bin/env python3

import sys
sys.path.append("..")

import gen_tests_makefile
from generate import TESTS

def create_tests():
    for t in TESTS:
        libs_args = ""
        for lib in t.libs:
            libs_args += f" -l memlib_{lib}.v"
        cmd = (
            f"../tools/autotest.sh -G -j ${{SEEDOPT}} ${{EXTRA_FLAGS}} "
            f"-p 'script ../t_{t.name}.ys'"
            f"{libs_args} "
            f"t_{t.name}.v >/dev/null 2>&1 || (cat t_{t.name}.err; exit 1)"
        )
        gen_tests_makefile.generate_target(t.name, cmd)

extra = [
    "SEED ?=",
    "ifneq ($(strip $(SEED)),)",
    "    SEEDOPT=-S$(SEED)",
    "endif",
]
gen_tests_makefile.generate_custom(create_tests, extra)
