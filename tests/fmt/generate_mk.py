#!/usr/bin/env python3

import sys
sys.path.append("..")

import gen_tests_makefile

def cmd(lines):
    return " ; \\\n".join(lines)

def initial_display():
    gen_tests_makefile.generate_target("initial_display", cmd([
        f"$(YOSYS) -p \"read_verilog initial_display.v\" | awk \"/<<<BEGIN>>>/,/<<<END>>>/ {{print $$0}}\" >yosys-initial_display.log 2>&1",
        "iverilog -o iverilog-initial_display initial_display.v",
        "./iverilog-initial_display >iverilog-initial_display.log",
        "diff yosys-initial_display.log iverilog-initial_display.log",
    ]))


def always_display():
    cases = [
        ("clk", "-DEVENT_CLK"),
        ("clk_rst", "-DEVENT_CLK_RST"),
        ("star", "-DEVENT_STAR"),
        ("clk_en", "-DEVENT_CLK -DCOND_EN"),
        ("clk_rst_en", "-DEVENT_CLK_RST -DCOND_EN"),
        ("star_en", "-DEVENT_STAR -DCOND_EN"),
    ]

    for name, defs in cases:
        gen_tests_makefile.generate_target(f"always_display_{name}", cmd([
            f"$(YOSYS) -p \"read_verilog {defs} always_display.v; proc; opt_expr -mux_bool; clean\" -o yosys-always_display-{name}-1.v >/dev/null 2>&1",
            f"$(YOSYS) -p \"read_verilog yosys-always_display-{name}-1.v; proc; opt_expr -mux_bool; clean\" -o yosys-always_display-{name}-2.v >/dev/null 2>&1",
            f"diff yosys-always_display-{name}-1.v yosys-always_display-{name}-2.v",
        ]))


def roundtrip():
    cases = [
        ("dec_unsigned", '-DBASE_DEC -DSIGN=""'),
        ("dec_signed", '-DBASE_DEC -DSIGN="signed"'),
        ("hex_unsigned", '-DBASE_HEX -DSIGN=""'),
        ("hex_signed", '-DBASE_HEX -DSIGN="signed"'),
        ("oct_unsigned", '-DBASE_HEX -DSIGN=""'),
        ("oct_signed", '-DBASE_HEX -DSIGN="signed"'),
        ("bin_unsigned", '-DBASE_HEX -DSIGN=""'),
        ("bin_signed", '-DBASE_HEX -DSIGN="signed"'),
    ]

    for name, defs in cases:
        gen_tests_makefile.generate_target(f"roundtrip_{name}", cmd([
            f"$(YOSYS) -p \"read_verilog {defs} roundtrip.v; proc; clean\" -o yosys-roundtrip-{name}-1.v >/dev/null 2>&1",
            f"$(YOSYS) -p \"read_verilog yosys-roundtrip-{name}-1.v; proc; clean\" -o yosys-roundtrip-{name}-2.v >/dev/null 2>&1",
            f"diff yosys-roundtrip-{name}-1.v yosys-roundtrip-{name}-2.v",

            f"iverilog {defs} -o iverilog-roundtrip-{name} roundtrip.v roundtrip_tb.v >/dev/null 2>&1",
            f"./iverilog-roundtrip-{name} >iverilog-roundtrip-{name}.log",

            f"iverilog {defs} -o iverilog-roundtrip-{name}-1 yosys-roundtrip-{name}-1.v roundtrip_tb.v >/dev/null 2>&1",
            f"./iverilog-roundtrip-{name}-1 >iverilog-roundtrip-{name}-1.log",

            f"iverilog {defs} -o iverilog-roundtrip-{name}-2 yosys-roundtrip-{name}-2.v roundtrip_tb.v >/dev/null 2>&1",
            f"./iverilog-roundtrip-{name}-2 >iverilog-roundtrip-{name}-2.log",

            f"diff iverilog-roundtrip-{name}.log iverilog-roundtrip-{name}-1.log",
            f"diff iverilog-roundtrip-{name}-1.log iverilog-roundtrip-{name}-2.log",
        ]))


def cxxrtl():
    cases = ["always_full", "always_comb"]

    for name in cases:
        gen_tests_makefile.generate_target(f"cxxrtl_{name}", cmd([
            f"$(YOSYS) -p \"read_verilog {name}.v; proc; clean; write_cxxrtl -print-output std::cerr yosys-{name}.cc\" >/dev/null 2>&1",
            f"$${{CXX:-g++}} -std=c++11 -o yosys-{name} -I../../backends/cxxrtl/runtime {name}_tb.cc -lstdc++",
            f"./yosys-{name} 2>yosys-{name}.log",

            f"iverilog -o iverilog-{name} {name}.v {name}_tb.v >/dev/null 2>&1",
            f"./iverilog-{name} | grep -v \"$finish called\" >iverilog-{name}.log",

            f"diff iverilog-{name}.log yosys-{name}.log",
        ]))


def extra():
    gen_tests_makefile.generate_target("always_full_equiv", cmd([
        "$(YOSYS) -p \"read_verilog always_full.v; prep; clean\" -o yosys-always_full-1.v >/dev/null 2>&1",
        "iverilog -o iverilog-always_full-1 yosys-always_full-1.v always_full_tb.v >/dev/null 2>&1",
        "./iverilog-always_full-1 | grep -v \"$finish called\" >iverilog-always_full-1.log",
        "diff iverilog-always_full.log iverilog-always_full-1.log",
    ]))

    gen_tests_makefile.generate_target("display_lm", cmd([
        "$(YOSYS) -p \"read_verilog display_lm.v\" >yosys-display_lm.log 2>&1",
        "$(YOSYS) -p \"read_verilog display_lm.v; write_cxxrtl yosys-display_lm.cc\" >/dev/null 2>&1",
        f"$${{CXX:-g++}} -std=c++11 -o yosys-display_lm_cc -I../../backends/cxxrtl/runtime display_lm_tb.cc -lstdc++",
        "./yosys-display_lm_cc >yosys-display_lm_cc.log",
        "for log in yosys-display_lm.log yosys-display_lm_cc.log; do "
        "grep \"^%l: \\\\bot\\$\" \"$log\" >/dev/null 2>&1; "
        "grep \"^%m: \\\\bot\\$\" \"$log\" >/dev/null 2>&1; "
        "done",
    ]))


def main():
    def callback():
        #initial_display()
        always_display()
        roundtrip()
        cxxrtl()
        #extra()

    gen_tests_makefile.generate_custom(callback)


if __name__ == "__main__":
    main()
