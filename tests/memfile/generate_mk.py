#!/usr/bin/env python3

import sys
sys.path.append("..")

import gen_tests_makefile

def create_tests():
    setup = "mkdir -p temp && cp content1.dat temp/content2.dat"

    gen_tests_makefile.generate_cmd_test("parent_content1", [
        f"{setup};",
        '(cd .. && $(YOSYS_ABS) -qp "read_verilog -defer memfile/memory.v;',
        'chparam -set MEMFILE \\"content1.dat\\" memory") >/dev/null 2>&1',
    ])

    gen_tests_makefile.generate_cmd_test("parent_content2_temp", [
        f"{setup};",
        '(cd .. && $(YOSYS_ABS) -qp "read_verilog -defer memfile/memory.v;',
        'chparam -set MEMFILE \\"temp/content2.dat\\" memory") >/dev/null 2>&1',
    ])

    gen_tests_makefile.generate_cmd_test("parent_content2_full", [
        f"{setup};",
        '(cd .. && $(YOSYS_ABS) -qp "read_verilog -defer memfile/memory.v;',
        'chparam -set MEMFILE \\"memfile/temp/content2.dat\\" memory") >/dev/null 2>&1',
    ])

    gen_tests_makefile.generate_cmd_test("same_content1", [
        f"{setup};",
        '$(YOSYS) -qp "read_verilog -defer memory.v;',
        'chparam -set MEMFILE \\"content1.dat\\" memory" >/dev/null 2>&1',
    ])

    gen_tests_makefile.generate_cmd_test("same_content2", [
        f"{setup};",
        '$(YOSYS) -qp "read_verilog -defer memory.v;',
        'chparam -set MEMFILE \\"temp/content2.dat\\" memory" >/dev/null 2>&1',
    ])

    gen_tests_makefile.generate_cmd_test("child_content1", [
        f"{setup};",
        '(cd temp && ../$(YOSYS) -qp "read_verilog -defer ../memory.v;',
        'chparam -set MEMFILE \\"content1.dat\\" memory") >/dev/null 2>&1',
    ])

    gen_tests_makefile.generate_cmd_test("child_content2_temp", [
        f"{setup};",
        '(cd temp && ../$(YOSYS) -qp "read_verilog -defer ../memory.v;',
        'chparam -set MEMFILE \\"temp/content2.dat\\" memory") >/dev/null 2>&1',
    ])

    gen_tests_makefile.generate_cmd_test("child_content2_direct", [
        f"{setup};",
        '(cd temp && ../$(YOSYS) -qp "read_verilog -defer ../memory.v;',
        'chparam -set MEMFILE \\"temp/content2.dat\\" memory") >/dev/null 2>&1',
    ])

    gen_tests_makefile.generate_cmd_test("fail_empty_filename",
        '! $(YOSYS) -qp "read_verilog memory.v" >/dev/null 2>&1')

    gen_tests_makefile.generate_cmd_test("fail_missing_file", [
        '! $(YOSYS) -qp "read_verilog -defer memory.v;',
        'chparam -set MEMFILE \\"content3.dat\\" memory" >/dev/null 2>&1',
    ])

extra = ["YOSYS_ABS := $(abspath $(YOSYS))"]
gen_tests_makefile.generate_custom(create_tests, extra)

