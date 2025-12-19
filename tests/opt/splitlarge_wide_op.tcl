proc op_name {op_number} {
	set op [expr $op_number >> 2]
	set b_signed [expr {$op_number & 1 ? "signed": "unsigned"}]
	set a_signed [expr {(($op_number & 2) >> 1) ? "signed": "unsigned"}]
	set cell "unknown"
	if { "$op" == "0" } {
		set cell "\$add"
	} elseif { "$op" == "1" } {
		set cell "\$sub"
	}
	return "$cell (a $a_signed, b $b_signed)"
}

proc predict_adder_count {in_width max_width op_number} {
	set b_signed [expr {$op_number & 1}]
	set a_signed [expr {($op_number & 2) >> 1}]
	set a_width [expr {$in_width + $a_signed}]
	set b_width [expr {$in_width + $b_signed}]

	set adder_width [expr {max($a_width, $b_width)}]
	set adder_queue [list]

	if {$adder_width > $max_width} {
			lappend adder_queue $adder_width
	}

	set adder_count 1

	while {[llength $adder_queue] > 0} {
			set current [lindex $adder_queue end]
			set adder_queue [lrange $adder_queue 0 end-1]

			incr adder_count 2 ;  # one changed adder, two new adders

			set low [expr {$current / 2}]
			set high [expr {$current - $low}]
			set carry [expr {$high + 1}]

			if {$low > $max_width} {
					lappend adder_queue $low
			}
			if {$high > $max_width} {
					lappend adder_queue $high
			}
			if {$carry > $max_width} {
					lappend adder_queue $carry
			}
	}
	return $adder_count
}

yosys -import
log -header "splitlarge"
log -push
for {set i 0} {$i < 8} {incr i} {
	log -header "[op_name $i]"
	log -push
	design -reset
	read_verilog wide_op.v
	hierarchy -top wide_op
	chparam -set width 1024 -set op $i wide_op
	yosys proc
	simplemap
	equiv_opt -post -assert splitlarge -max_width 128
	yosys select -assert-none r:A_WIDTH>128
	yosys select -assert-none r:B_WIDTH>128
	yosys select -assert-count [predict_adder_count 1024 128 $i] r:A_WIDTH
	log -pop
}
log -pop
