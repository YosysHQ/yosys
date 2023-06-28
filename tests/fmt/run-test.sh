#!/bin/bash

set -ex

../../yosys -p 'read_verilog initial_display.v' | awk '/<<<BEGIN>>>/,/<<<END>>>/ {print $0}' >yosys-initial_display.log
iverilog -o iverilog-initial_display initial_display.v
./iverilog-initial_display >iverilog-initial_display.log
diff yosys-initial_display.log iverilog-initial_display.log

test_always_display () {
	local subtest=$1; shift
	../../yosys -p "read_verilog $* always_display.v; proc; opt_expr -mux_bool; clean" -o yosys-always_display-${subtest}-1.v
	../../yosys -p "read_verilog yosys-always_display-${subtest}-1.v; proc; opt_expr -mux_bool; clean" -o yosys-always_display-${subtest}-2.v
	diff yosys-always_display-${subtest}-1.v yosys-always_display-${subtest}-2.v
}

test_always_display clk -DEVENT_CLK
test_always_display clk_rst -DEVENT_CLK_RST
test_always_display star -DEVENT_STAR

test_always_display clk_en -DEVENT_CLK -DCOND_EN
test_always_display clk_rst_en -DEVENT_CLK_RST -DCOND_EN
test_always_display star_en -DEVENT_STAR -DCOND_EN

test_roundtrip () {
	local subtest=$1; shift
	../../yosys -p "read_verilog $* roundtrip.v; proc; clean" -o yosys-roundtrip-${subtest}-1.v
	../../yosys -p "read_verilog yosys-roundtrip-${subtest}-1.v; proc; clean" -o yosys-roundtrip-${subtest}-2.v
	diff yosys-roundtrip-${subtest}-1.v yosys-roundtrip-${subtest}-2.v

	iverilog $* -o iverilog-roundtrip-${subtest} roundtrip.v roundtrip_tb.v
	./iverilog-roundtrip-${subtest} >iverilog-roundtrip-${subtest}.log
	iverilog $* -o iverilog-roundtrip-${subtest}-1 yosys-roundtrip-${subtest}-1.v roundtrip_tb.v
	./iverilog-roundtrip-${subtest}-1 >iverilog-roundtrip-${subtest}-1.log
	iverilog $* -o iverilog-roundtrip-${subtest}-2 yosys-roundtrip-${subtest}-2.v roundtrip_tb.v
	./iverilog-roundtrip-${subtest}-1 >iverilog-roundtrip-${subtest}-2.log
	diff iverilog-roundtrip-${subtest}.log iverilog-roundtrip-${subtest}-1.log
	diff iverilog-roundtrip-${subtest}-1.log iverilog-roundtrip-${subtest}-2.log
}

test_roundtrip dec_unsigned -DBASE_DEC -DSIGN=""
test_roundtrip dec_signed -DBASE_DEC -DSIGN="signed"
test_roundtrip hex_unsigned -DBASE_HEX -DSIGN=""
test_roundtrip hex_signed -DBASE_HEX -DSIGN="signed"
test_roundtrip oct_unsigned -DBASE_HEX -DSIGN=""
test_roundtrip oct_signed -DBASE_HEX -DSIGN="signed"
test_roundtrip bin_unsigned -DBASE_HEX -DSIGN=""
test_roundtrip bin_signed -DBASE_HEX -DSIGN="signed"

../../yosys -p "read_verilog always_full.v; write_cxxrtl yosys-always_full.cc"
${CXX:-g++} -o yosys-always_full -I../.. always_full_tb.cc
./yosys-always_full >yosys-always_full.log
iverilog -o iverilog-always_full always_full.v always_full_tb.v
./iverilog-always_full | awk '/<<<BEGIN>>>/,/<<<END>>>/ {print $0}' >iverilog-always_full.log
diff iverilog-always_full.log yosys-always_full.log
