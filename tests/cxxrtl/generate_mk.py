#!/usr/bin/env python3

import sys
sys.path.append("..")

import gen_tests_makefile

def run_subtest(name):
    gen_tests_makefile.generate_cmd_test(f"cxxrtl_{name}", [
        f"$${{CXX:-g++}} -std=c++11 -O2 -o cxxrtl-test-{name} -I../../backends/cxxrtl/runtime test_{name}.cc -lstdc++",
        f"./cxxrtl-test-{name}",
    ])

def compile_only():
    gen_tests_makefile.generate_cmd_test("cxxrtl_unconnected_output", [
        '$(YOSYS) -p "read_verilog test_unconnected_output.v; select =*; proc; clean; write_cxxrtl cxxrtl-test-unconnected_output.cc"',
        f'$${{CXX:-g++}} -std=c++11 -c -o cxxrtl-test-unconnected_output -I../../backends/cxxrtl/runtime cxxrtl-test-unconnected_output.cc',
    ])

def main():
    def callback():
        run_subtest("value")
        run_subtest("value_fuzz")
        compile_only()

    gen_tests_makefile.generate_custom(callback)

if __name__ == "__main__":
    main()
