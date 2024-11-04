yosys read_verilog tcl_apis.v

if {[rtlil::get_attr -string -mod top foo] != "bar"} {
	error "bad top module attribute"
}

if {[rtlil::get_attr -bool top w dont_touch] != 1} {
	error "bad w wire attribute"
}

if {[rtlil::get_param -int top inst PARAM] != 4} {
	error "bad parameter"
}

rtlil::set_attr -true -mod top marked
yosys select -assert-any A:marked
