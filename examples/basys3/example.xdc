
set_property -dict { IOSTANDARD LVCMOS33 PACKAGE_PIN W5  } [get_ports CLK]
set_property -dict { IOSTANDARD LVCMOS33 PACKAGE_PIN U16 } [get_ports {LD[0]}]
set_property -dict { IOSTANDARD LVCMOS33 PACKAGE_PIN E19 } [get_ports {LD[1]}]
set_property -dict { IOSTANDARD LVCMOS33 PACKAGE_PIN U19 } [get_ports {LD[2]}]
set_property -dict { IOSTANDARD LVCMOS33 PACKAGE_PIN V19 } [get_ports {LD[3]}]
set_property -dict { IOSTANDARD LVCMOS33 PACKAGE_PIN W18 } [get_ports {LD[4]}]
set_property -dict { IOSTANDARD LVCMOS33 PACKAGE_PIN U15 } [get_ports {LD[5]}]
set_property -dict { IOSTANDARD LVCMOS33 PACKAGE_PIN U14 } [get_ports {LD[6]}]
set_property -dict { IOSTANDARD LVCMOS33 PACKAGE_PIN V14 } [get_ports {LD[7]}]
set_property -dict { IOSTANDARD LVCMOS33 PACKAGE_PIN V13 } [get_ports {LD[8]}]
set_property -dict { IOSTANDARD LVCMOS33 PACKAGE_PIN V3  } [get_ports {LD[9]}]
set_property -dict { IOSTANDARD LVCMOS33 PACKAGE_PIN W3  } [get_ports {LD[10]}]
set_property -dict { IOSTANDARD LVCMOS33 PACKAGE_PIN U3  } [get_ports {LD[11]}]
set_property -dict { IOSTANDARD LVCMOS33 PACKAGE_PIN P3  } [get_ports {LD[12]}]
set_property -dict { IOSTANDARD LVCMOS33 PACKAGE_PIN N3  } [get_ports {LD[13]}]
set_property -dict { IOSTANDARD LVCMOS33 PACKAGE_PIN P1  } [get_ports {LD[14]}]
set_property -dict { IOSTANDARD LVCMOS33 PACKAGE_PIN L1  } [get_ports {LD[15]}]

create_clock -add -name sys_clk_pin -period 10.00 -waveform {0 5} [get_ports CLK]

set_property CONFIG_VOLTAGE 3.3 [current_design]
set_property CFGBVS VCCO [current_design]

