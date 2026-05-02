yosys -import

set tmp_v "opt_boundary_random_tmp.v"

proc emit_case {case_id width op0 op1 op2} {
	global tmp_v

	set fh [open $tmp_v w]
	puts $fh "module m(input \[$width-1:0\] a, input \[$width-1:0\] b, input \[$width-1:0\] c, input \[$width-1:0\] d, output \[$width-1:0\] y);"
	puts $fh "  wire \[$width-1:0\] t0 = a $op0 b;"
	puts $fh "  wire \[$width-1:0\] t1 = t0 $op1 c;"
	puts $fh "  assign y = t1 $op2 d;"
	puts $fh "endmodule"
	puts $fh ""
	puts $fh "module top(input \[$width-1:0\] a, input \[$width-1:0\] b, input \[$width-1:0\] c, input \[$width-1:0\] d, output \[$width-1:0\] y);"
	puts $fh "  genvar i;"
	puts $fh "  generate"
	puts $fh "    for (i = 0; i < 4; i = i + 1) begin : gen"
	puts $fh "      m u(.a({a\[$width-2:0\], a\[$width-1\]}), .b(b), .c(c), .d(d), .y(y));"
	puts $fh "    end"
	puts $fh "  endgenerate"
	puts $fh "endmodule"
	close $fh

	log -header "randomized boundary case $case_id"
	log -push
	design -reset
	read_verilog $tmp_v
	hierarchy -top top
	yosys proc
	opt_expr
	opt_clean
	design -save start
	flatten
	design -save gold
	design -load start
	opt_boundary -max_cells 4
	opt_clean
	flatten
	design -save gate

	design -reset
	design -copy-from gold -as gold A:top
	design -copy-from gate -as gate A:top
	yosys rename -hide
	equiv_make gold gate equiv
	equiv_simple equiv
	equiv_status -assert equiv
	log -pop
}

set ops [list "&" "|" "^"]
for {set i 0} {$i < 12} {incr i} {
	set width [expr {2 + ($i % 5)}]
	set op0 [lindex $ops [expr {$i % 3}]]
	set op1 [lindex $ops [expr {($i / 3) % 3}]]
	set op2 [lindex $ops [expr {($i / 9) % 3}]]
	emit_case $i $width $op0 $op1 $op2
}

file delete -force $tmp_v
