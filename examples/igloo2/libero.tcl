# Run with "libero SCRIPT:libero.tcl"

new_project \
    -name top \
    -location work \
    -family IGLOO2 \
    -die PA4MGL500 \
    -package tq144 \
    -speed -1 \
    -hdl VERILOG

# import_files -edif "[pwd]/netlist.edn"

import_files -hdl_source "[pwd]/netlist.v"
set_root top

save_project

puts "**> SYNTHESIZE"
run_tool -name {SYNTHESIZE}
puts "<** SYNTHESIZE"

puts "**> COMPILE"
run_tool -name {COMPILE}
puts "<** COMPILE"

puts "**> PLACEROUTE"
run_tool -name {PLACEROUTE}
puts "<** PLACEROUTE"

# puts "**> export_bitstream"
# export_bitstream_file -trusted_facility_file 1 -trusted_facility_file_components {FABRIC}
# puts "<** export_bitstream"

exit 0
