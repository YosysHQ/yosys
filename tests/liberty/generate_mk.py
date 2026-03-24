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
            f'$(YOSYS) -p "read_verilog small.v; synth -top small; dfflibmap -info -liberty {lib}" -ql {base}.log;',

            f'../../yosys-filterlib - {lib} 2>/dev/null > {lib}.filtered;',
            f'../../yosys-filterlib -verilogsim {lib} > {lib}.verilogsim;',

            f'diff {lib}.filtered {lib}.filtered.ok;',
            f'diff {lib}.verilogsim {lib}.verilogsim.ok;',

            f'if [ -e {base}.log.ok ]; then '
            f'$(YOSYS) -p "dfflibmap -info -liberty {lib}" -TqqQl {base}.log >/dev/null 2>&1; '
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

    gen_tests_makefile.generate_custom(callback)


if __name__ == "__main__":
    main()
