#!/usr/bin/env bash

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

test_cxxrtl () {
	local subtest=$1; shift

	../../yosys -p "read_verilog ${subtest}.v; proc; clean; write_cxxrtl -print-output std::cerr yosys-${subtest}.cc"
	${CC:-gcc} -std=c++11 -o yosys-${subtest} -I../../backends/cxxrtl/runtime ${subtest}_tb.cc -lstdc++
	./yosys-${subtest} 2>yosys-${subtest}.log
	iverilog -o iverilog-${subtest} ${subtest}.v ${subtest}_tb.v
	./iverilog-${subtest} |grep -v '\$finish called' >iverilog-${subtest}.log
	diff iverilog-${subtest}.log yosys-${subtest}.log
}

test_cxxrtl always_full
test_cxxrtl always_comb

# Ensure Verilog backend preserves behaviour of always block with multiple $displays.
../../yosys -p "read_verilog always_full.v; prep; clean" -o yosys-always_full-1.v
iverilog -o iverilog-always_full-1 yosys-always_full-1.v always_full_tb.v
./iverilog-always_full-1 |grep -v '\$finish called' >iverilog-always_full-1.log
diff iverilog-always_full.log iverilog-always_full-1.log

../../yosys -p "read_verilog display_lm.v" >yosys-display_lm.log
../../yosys -p "read_verilog display_lm.v; write_cxxrtl yosys-display_lm.cc"
${CC:-gcc} -std=c++11 -o yosys-display_lm_cc -I../../backends/cxxrtl/runtime display_lm_tb.cc -lstdc++
./yosys-display_lm_cc >yosys-display_lm_cc.log
for log in yosys-display_lm.log yosys-display_lm_cc.log; do
	grep "^%l: \\\\bot\$" "$log"
	grep "^%m: \\\\bot\$" "$log"
done
