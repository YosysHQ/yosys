puts "SDC constraints file says hello from arbitrary Tcl execution"
set_false_path -from [get_pins s1/sa] -to [get_pins s1/sb]
puts "This should print something:"
puts [get_ports a b]
puts "Did it?"