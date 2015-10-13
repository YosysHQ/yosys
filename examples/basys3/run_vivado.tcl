read_xdc example.xdc
read_edif example.edif
link_design -part xc7a35tcpg236-1 -top example
opt_design
place_design
route_design
report_utilization
report_timing
write_bitstream -force example.bit
