###############################################################################
# Created by write_sdc
# Fri Oct  3 11:26:00 2025
###############################################################################
current_design wrapper
###############################################################################
# Timing Constraints
###############################################################################
create_clock -name this_clk -period 1.0000 [get_ports {clk}]
create_clock -name that_clk -period 2.0000 
create_clock -name another_clk -period 2.0000 \
    [list [get_ports {A[0]}]\
          [get_ports {A[1]}]\
          [get_ports {A[2]}]\
          [get_ports {A[3]}]\
          [get_ports {A[4]}]\
          [get_ports {A[5]}]\
          [get_ports {A[6]}]\
          [get_ports {A[7]}]\
          [get_ports {B[0]}]\
          [get_ports {B[1]}]\
          [get_ports {B[2]}]\
          [get_ports {B[3]}]\
          [get_ports {B[4]}]\
          [get_ports {B[5]}]\
          [get_ports {B[6]}]\
          [get_ports {B[7]}]]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -rise -min -add_delay [get_ports {A[0]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -fall -min -add_delay [get_ports {A[0]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -rise -min -add_delay [get_ports {A[1]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -fall -min -add_delay [get_ports {A[1]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -rise -min -add_delay [get_ports {A[2]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -fall -min -add_delay [get_ports {A[2]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -rise -min -add_delay [get_ports {A[3]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -fall -min -add_delay [get_ports {A[3]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -rise -min -add_delay [get_ports {A[4]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -fall -min -add_delay [get_ports {A[4]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -rise -min -add_delay [get_ports {A[5]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -fall -min -add_delay [get_ports {A[5]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -rise -min -add_delay [get_ports {A[6]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -fall -min -add_delay [get_ports {A[6]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -rise -min -add_delay [get_ports {A[7]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -fall -min -add_delay [get_ports {A[7]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -rise -min -add_delay [get_ports {B[0]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -fall -min -add_delay [get_ports {B[0]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -rise -min -add_delay [get_ports {B[1]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -fall -min -add_delay [get_ports {B[1]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -rise -min -add_delay [get_ports {B[2]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -fall -min -add_delay [get_ports {B[2]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -rise -min -add_delay [get_ports {B[3]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -fall -min -add_delay [get_ports {B[3]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -rise -min -add_delay [get_ports {B[4]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -fall -min -add_delay [get_ports {B[4]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -rise -min -add_delay [get_ports {B[5]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -fall -min -add_delay [get_ports {B[5]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -rise -min -add_delay [get_ports {B[6]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -fall -min -add_delay [get_ports {B[6]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -rise -min -add_delay [get_ports {B[7]}]
set_input_delay 1.0000 -clock [get_clocks {this_clk}] -fall -min -add_delay [get_ports {B[7]}]
group_path -name operation_group\
    -through [list [get_nets {alu/operation[0]}]\
           [get_nets {alu/operation[1]}]\
           [get_nets {alu/operation[2]}]\
           [get_nets {alu/operation[3]}]]
###############################################################################
# Environment
###############################################################################
###############################################################################
# Design Rules
###############################################################################
