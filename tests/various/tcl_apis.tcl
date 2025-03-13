yosys read_verilog tcl_apis.v

if {[rtlil::get_attr -string -mod top foo] != "bar"} {
	error "bad top module attribute"
}

if {[rtlil::get_attr -int -mod top val] != 4294967295} {
	error "bad top module attribute 2"
}

if {[rtlil::get_attr -sint -mod top val] != -1} {
	error "bad top module attribute 3"
}

if {[rtlil::get_attr -bool top w dont_touch] != 1} {
	error "bad w wire attribute"
}

if {[rtlil::get_param -int top inst PARAM] != -3} {
	error "bad parameter"
}
if {[rtlil::get_param -uint top inst PARAM] != 4294967293} {
	error "bad parameter 2"
}

rtlil::set_attr -true -mod top marked
yosys select -assert-any A:marked

# write a 32-bit constant with most bits set
rtlil::set_attr -mod -uint top f 4294967294
# read it back as a signed integer
if {[rtlil::get_attr -mod -sint top f] != -2} {
	error "bad int roundtrip"
}
# read it back as an unsigned integer (no signedness flag)
if {[rtlil::get_attr -mod -int top f] != 4294967294} {
	error "bad int roundtrip 2"
}
# read it back as an unsigned integer
if {[rtlil::get_attr -mod -uint top f] != 4294967294} {
	error "bad int roundtrip 3"
}

# write a signed 32-bit constant
rtlil::set_attr -mod -sint top f -3
# read it back as a signed integer
if {[rtlil::get_attr -mod -sint top f] != -3} {
	error "bad int roundtrip 4"
}
# read it back as a signed integer (due to signedness flag)
if {[rtlil::get_attr -mod -int top f] != -3} {
	error "bad int roundtrip 5"
}
# read it back as an unsigned integer
if {[rtlil::get_attr -mod -uint top f] != 4294967293} {
	error "bad int roundtrip 6"
}

# write a constant larger than 32 bits
rtlil::set_attr -mod -sint top prime 87178291199
if {[rtlil::get_attr -mod -int top prime] != 87178291199} {
	error "bad int roundtrip 7"
}
