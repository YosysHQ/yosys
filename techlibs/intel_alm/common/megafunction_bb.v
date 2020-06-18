// Intel megafunction declarations, to avoid Yosys complaining.
`default_nettype none

(* blackbox *)
module altera_std_synchronizer(clk, din, dout, reset_n);

parameter depth = 2;

input clk;
input reset_n;
input din;
output dout;

endmodule

(* blackbox *)
module altiobuf_in(datain, dataout);

parameter enable_bus_hold = "FALSE";
parameter use_differential_mode = "FALSE";
parameter number_of_channels = 1;

input [number_of_channels-1:0] datain;
output [number_of_channels-1:0] dataout;

endmodule

(* blackbox *)
module altiobuf_out(datain, dataout);

parameter enable_bus_hold = "FALSE";
parameter use_differential_mode = "FALSE";
parameter use_oe = "FALSE";
parameter number_of_channels = 1;

input [number_of_channels-1:0] datain;
output [number_of_channels-1:0] dataout;

endmodule

(* blackbox *)
module altiobuf_bidir(dataio, oe, datain, dataout);

parameter number_of_channels = 1;
parameter enable_bus_hold = "OFF";

inout [number_of_channels-1:0] dataio;
input [number_of_channels-1:0] datain;
output [number_of_channels-1:0] dataout;
input [number_of_channels-1:0] oe;

endmodule

(* blackbox *)
module altsyncram(clock0, clock1, address_a, data_a, rden_a, wren_a, byteena_a, q_a, addressstall_a, address_b, data_b, rden_b, wren_b, byteena_b, q_b, addressstall_b, clocken0, clocken1, clocken2, clocken3, aclr0, aclr1, eccstatus);

parameter lpm_type = "altsyncram";
parameter operation_mode = "dual_port";
parameter ram_block_type = "auto";
parameter intended_device_family = "auto";
parameter power_up_uninitialized = "false";
parameter read_during_write_mode_mixed_ports = "dontcare";
parameter byte_size = 8;
parameter widthad_a = 1;
parameter width_a = 1;
parameter width_byteena_a = 1;
parameter numwords_a = 1;
parameter clock_enable_input_a = "clocken0";
parameter widthad_b = 1;
parameter width_b = 1;
parameter numwords_b = 1;
parameter address_aclr_b = "aclr0";
parameter address_reg_b = "";
parameter outdata_aclr_b = "aclr0";
parameter outdata_reg_b = "";
parameter clock_enable_input_b = "clocken0";
parameter clock_enable_output_b = "clocken0";

input clock0, clock1;
input [widthad_a-1:0] address_a;
input [width_a-1:0] data_a;
input rden_a;
input wren_a;
input [(width_a/8)-1:0] byteena_a;
input addressstall_a;

output [width_a-1:0] q_a;

input wren_b;
input rden_b;
input [widthad_b-1:0] address_b;
input [width_b-1:0] data_b;
input [(width_b/8)-1:0] byteena_b;
input addressstall_b;

output [width_b-1:0] q_b;

input clocken0;
input clocken1;
input clocken2;
input clocken3;

input aclr0;
input aclr1;

output eccstatus;

endmodule

(* blackbox *)
module cyclonev_mlab_cell(portaaddr, portadatain, portbaddr, portbdataout, ena0, clk0, clk1);

parameter logical_ram_name = "";
parameter logical_ram_depth = 32;
parameter logical_ram_width = 20;
parameter mixed_port_feed_through_mode = "new";
parameter first_bit_number = 0;
parameter first_address = 0;
parameter last_address = 31;
parameter address_width = 5;
parameter data_width = 1;
parameter byte_enable_mask_width = 1;
parameter port_b_data_out_clock = "NONE";
parameter [639:0] mem_init0 = 640'b0;

input [address_width-1:0] portaaddr, portbaddr;
input [data_width-1:0] portadatain;
output [data_width-1:0] portbdataout;
input ena0, clk0, clk1;

endmodule
