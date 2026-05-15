#!/usr/bin/env python3

import glob
import os
import sys
sys.path.append("..")

import gen_tests_makefile

def lib_tests():
    for lib in sorted(glob.glob("*.lib")):
        base = os.path.splitext(lib)[0]

        gen_tests_makefile.generate_cmd_test(lib, [
            f'$(YOSYS) -p "read_verilog small.v; synth -top small; dfflibmap -info -liberty {lib}" -ql {base}.log',

            f'$(YOSYS_FILTERLIB) - {lib} > {lib}.filtered',
            f'$(YOSYS_FILTERLIB) -verilogsim {lib} > {lib}.verilogsim',

            f'diff {lib}.filtered {lib}.filtered.ok',
            f'diff {lib}.verilogsim {lib}.verilogsim.ok',

            f'if [ -e {base}.log.ok ]; then '
            f'$(YOSYS) -p "dfflibmap -info -liberty {lib}" -TqqQl {base}.log; '
            f'diff {base}.log {base}.log.ok; '
            f'fi',
        ])


def ys_tests():
    for ys in sorted(glob.glob("*.ys")):
        gen_tests_makefile.generate_ys_test(ys)

def main():
    def callback():
        lib_tests()
        ys_tests()

    gen_tests_makefile.generate_custom(callback,
        [f"YOSYS_FILTERLIB ?= {gen_tests_makefile.yosys_basedir}/yosys-filterlib"])


if __name__ == "__main__":
    main()
