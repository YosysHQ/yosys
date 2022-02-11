// Intel megafunction declarations, to avoid Yosys complaining.
`default_nettype none

(* blackbox *)
module altera_pll
#(
    parameter reference_clock_frequency       = "0 ps",
	parameter fractional_vco_multiplier       = "false",
    parameter pll_type                        = "General",
    parameter pll_subtype                     = "General",
    parameter number_of_clocks                   = 1,
    parameter operation_mode                  = "internal feedback",
    parameter deserialization_factor           = 4,
    parameter data_rate                       = 0,
    
    parameter sim_additional_refclk_cycles_to_lock      = 0,
    parameter output_clock_frequency0           = "0 ps",
    parameter phase_shift0                      = "0 ps",
    parameter duty_cycle0                      = 50,
    
    parameter output_clock_frequency1           = "0 ps",
    parameter phase_shift1                      = "0 ps",
    parameter duty_cycle1                      = 50,
    
    parameter output_clock_frequency2           = "0 ps",
    parameter phase_shift2                      = "0 ps",
    parameter duty_cycle2                      = 50,
    
    parameter output_clock_frequency3           = "0 ps",
    parameter phase_shift3                      = "0 ps",
    parameter duty_cycle3                      = 50,
    
    parameter output_clock_frequency4           = "0 ps",
    parameter phase_shift4                      = "0 ps",
    parameter duty_cycle4                      = 50,
    
    parameter output_clock_frequency5           = "0 ps",
    parameter phase_shift5                      = "0 ps",
    parameter duty_cycle5                      = 50,
    
    parameter output_clock_frequency6           = "0 ps",
    parameter phase_shift6                      = "0 ps",
    parameter duty_cycle6                      = 50,
    
    parameter output_clock_frequency7           = "0 ps",
    parameter phase_shift7                      = "0 ps",
    parameter duty_cycle7                      = 50,
    
    parameter output_clock_frequency8           = "0 ps",
    parameter phase_shift8                      = "0 ps",
    parameter duty_cycle8                      = 50,
    
    parameter output_clock_frequency9           = "0 ps",
    parameter phase_shift9                      = "0 ps",
    parameter duty_cycle9                      = 50,    

    
    parameter output_clock_frequency10           = "0 ps",
    parameter phase_shift10                      = "0 ps",
    parameter duty_cycle10                      = 50,
    
    parameter output_clock_frequency11           = "0 ps",
    parameter phase_shift11                      = "0 ps",
    parameter duty_cycle11                      = 50,
    
    parameter output_clock_frequency12           = "0 ps",
    parameter phase_shift12                      = "0 ps",
    parameter duty_cycle12                      = 50,
    
    parameter output_clock_frequency13           = "0 ps",
    parameter phase_shift13                      = "0 ps",
    parameter duty_cycle13                      = 50,
    
    parameter output_clock_frequency14           = "0 ps",
    parameter phase_shift14                      = "0 ps",
    parameter duty_cycle14                      = 50,
    
    parameter output_clock_frequency15           = "0 ps",
    parameter phase_shift15                      = "0 ps",
    parameter duty_cycle15                      = 50,
    
    parameter output_clock_frequency16           = "0 ps",
    parameter phase_shift16                      = "0 ps",
    parameter duty_cycle16                      = 50,
    
    parameter output_clock_frequency17           = "0 ps",
    parameter phase_shift17                      = "0 ps",
    parameter duty_cycle17                      = 50,
    
    parameter clock_name_0 = "",
    parameter clock_name_1 = "",
    parameter clock_name_2 = "",
    parameter clock_name_3 = "",
    parameter clock_name_4 = "",
    parameter clock_name_5 = "",
    parameter clock_name_6 = "",
    parameter clock_name_7 = "",
    parameter clock_name_8 = "",

    parameter clock_name_global_0 = "false",
    parameter clock_name_global_1 = "false",
    parameter clock_name_global_2 = "false",
    parameter clock_name_global_3 = "false",
    parameter clock_name_global_4 = "false",
    parameter clock_name_global_5 = "false",
    parameter clock_name_global_6 = "false",
    parameter clock_name_global_7 = "false",
    parameter clock_name_global_8 = "false",

    parameter m_cnt_hi_div                       = 1,
    parameter m_cnt_lo_div                       = 1,
    parameter m_cnt_bypass_en                   = "false",
    parameter m_cnt_odd_div_duty_en           = "false",
    parameter n_cnt_hi_div                       = 1,
    parameter n_cnt_lo_div                       = 1,
    parameter n_cnt_bypass_en                   = "false",
    parameter n_cnt_odd_div_duty_en           = "false",
    parameter c_cnt_hi_div0                      = 1, 
    parameter c_cnt_lo_div0                      = 1,
    parameter c_cnt_bypass_en0                  = "false",
	parameter c_cnt_in_src0                     = "ph_mux_clk",
    parameter c_cnt_odd_div_duty_en0              = "false",
    parameter c_cnt_prst0                  = 1,
    parameter c_cnt_ph_mux_prst0                  = 0,
    parameter c_cnt_hi_div1                      = 1, 
    parameter c_cnt_lo_div1                      = 1,
    parameter c_cnt_bypass_en1                  = "false",
	parameter c_cnt_in_src1                     = "ph_mux_clk",
    parameter c_cnt_odd_div_duty_en1              = "false",
    parameter c_cnt_prst1                  = 1,
    parameter c_cnt_ph_mux_prst1                  = 0,
    parameter c_cnt_hi_div2                      = 1, 
    parameter c_cnt_lo_div2                                              = 1,
    parameter c_cnt_bypass_en2                  = "false",
	parameter c_cnt_in_src2                     = "ph_mux_clk",
    parameter c_cnt_odd_div_duty_en2 = "false",
    parameter c_cnt_prst2                  = 1,
    parameter c_cnt_ph_mux_prst2                  = 0,
    parameter c_cnt_hi_div3                      = 1, 
    parameter c_cnt_lo_div3                                              = 1,
    parameter c_cnt_bypass_en3                  = "false",
	parameter c_cnt_in_src3                     = "ph_mux_clk",
    parameter c_cnt_odd_div_duty_en3 = "false",
    parameter c_cnt_prst3                  = 1,
    parameter c_cnt_ph_mux_prst3                  = 0,
    parameter c_cnt_hi_div4                      = 1, 
    parameter c_cnt_lo_div4                                              = 1,
    parameter c_cnt_bypass_en4                  = "false",
	parameter c_cnt_in_src4                     = "ph_mux_clk",
    parameter c_cnt_odd_div_duty_en4 = "false",
    parameter c_cnt_prst4                  = 1,
    parameter c_cnt_ph_mux_prst4                  = 0,
    parameter c_cnt_hi_div5                      = 1, 
    parameter c_cnt_lo_div5                                              = 1,
    parameter c_cnt_bypass_en5                  = "false",
	parameter c_cnt_in_src5                     = "ph_mux_clk",
    parameter c_cnt_odd_div_duty_en5 = "false",
    parameter c_cnt_prst5                  = 1,
    parameter c_cnt_ph_mux_prst5                  = 0,
    parameter c_cnt_hi_div6                      = 1, 
    parameter c_cnt_lo_div6                                              = 1,
    parameter c_cnt_bypass_en6                  = "false",
	parameter c_cnt_in_src6                     = "ph_mux_clk",
    parameter c_cnt_odd_div_duty_en6 = "false",
    parameter c_cnt_prst6                  = 1,
    parameter c_cnt_ph_mux_prst6                  = 0,
    parameter c_cnt_hi_div7                      = 1, 
    parameter c_cnt_lo_div7                                              = 1,
    parameter c_cnt_bypass_en7                  = "false",
	parameter c_cnt_in_src7                     = "ph_mux_clk",
    parameter c_cnt_odd_div_duty_en7 = "false",
    parameter c_cnt_prst7                  = 1,
    parameter c_cnt_ph_mux_prst7                  = 0,
    parameter c_cnt_hi_div8                      = 1, 
    parameter c_cnt_lo_div8                                              = 1,
    parameter c_cnt_bypass_en8                  = "false",
	parameter c_cnt_in_src8                     = "ph_mux_clk",
    parameter c_cnt_odd_div_duty_en8 = "false",
    parameter c_cnt_prst8                  = 1,
    parameter c_cnt_ph_mux_prst8                  = 0,
    parameter c_cnt_hi_div9                      = 1, 
    parameter c_cnt_lo_div9                                              = 1,
    parameter c_cnt_bypass_en9                  = "false",
	parameter c_cnt_in_src9                     = "ph_mux_clk",
    parameter c_cnt_odd_div_duty_en9 = "false",
    parameter c_cnt_prst9                  = 1,
    parameter c_cnt_ph_mux_prst9                  = 0,
    parameter c_cnt_hi_div10                      = 1, 
    parameter c_cnt_lo_div10                                              = 1,
    parameter c_cnt_bypass_en10                  = "false",
	parameter c_cnt_in_src10                     = "ph_mux_clk",
    parameter c_cnt_odd_div_duty_en10 = "false",
    parameter c_cnt_prst10                  = 1,
    parameter c_cnt_ph_mux_prst10                  = 0,
    parameter c_cnt_hi_div11                      = 1, 
    parameter c_cnt_lo_div11                                              = 1,
    parameter c_cnt_bypass_en11                  = "false",
	parameter c_cnt_in_src11                     = "ph_mux_clk",
    parameter c_cnt_odd_div_duty_en11 = "false",
    parameter c_cnt_prst11                  = 1,
    parameter c_cnt_ph_mux_prst11                  = 0,
    parameter c_cnt_hi_div12                      = 1, 
    parameter c_cnt_lo_div12                                              = 1,
    parameter c_cnt_bypass_en12                  = "false",
	parameter c_cnt_in_src12                     = "ph_mux_clk",
    parameter c_cnt_odd_div_duty_en12 = "false",
    parameter c_cnt_prst12                  = 1,
    parameter c_cnt_ph_mux_prst12                  = 0,
    parameter c_cnt_hi_div13                      = 1, 
    parameter c_cnt_lo_div13                                              = 1,
    parameter c_cnt_bypass_en13                  = "false",
	parameter c_cnt_in_src13                     = "ph_mux_clk",
    parameter c_cnt_odd_div_duty_en13 = "false",
    parameter c_cnt_prst13                  = 1,
    parameter c_cnt_ph_mux_prst13                  = 0,
    parameter c_cnt_hi_div14                      = 1, 
    parameter c_cnt_lo_div14                                              = 1,
    parameter c_cnt_bypass_en14                  = "false",
	parameter c_cnt_in_src14                     = "ph_mux_clk",
    parameter c_cnt_odd_div_duty_en14 = "false",
    parameter c_cnt_prst14                  = 1,
    parameter c_cnt_ph_mux_prst14                  = 0,
    parameter c_cnt_hi_div15                      = 1, 
    parameter c_cnt_lo_div15                                              = 1,
    parameter c_cnt_bypass_en15                  = "false",
	parameter c_cnt_in_src15                     = "ph_mux_clk",
    parameter c_cnt_odd_div_duty_en15 = "false",
    parameter c_cnt_prst15                  = 1,
    parameter c_cnt_ph_mux_prst15                  = 0,
    parameter c_cnt_hi_div16                      = 1, 
    parameter c_cnt_lo_div16                                              = 1,
    parameter c_cnt_bypass_en16                  = "false",
	parameter c_cnt_in_src16                     = "ph_mux_clk",
    parameter c_cnt_odd_div_duty_en16 = "false",
    parameter c_cnt_prst16                  = 1,
    parameter c_cnt_ph_mux_prst16                  = 0,
    parameter c_cnt_hi_div17                      = 1, 
    parameter c_cnt_lo_div17                                              = 1,
    parameter c_cnt_bypass_en17                  = "false",
	parameter c_cnt_in_src17                     = "ph_mux_clk",
    parameter c_cnt_odd_div_duty_en17 = "false",
    parameter c_cnt_prst17                  = 1,
    parameter c_cnt_ph_mux_prst17                  = 0,
    parameter pll_vco_div = 1,
	parameter pll_slf_rst = "false",
	parameter pll_bw_sel = "low",
    parameter pll_output_clk_frequency = "0 MHz",
    parameter pll_cp_current = 0,
    parameter pll_bwctrl = 0,
    parameter pll_fractional_division = 1,
    parameter pll_fractional_cout = 24,
    parameter pll_dsm_out_sel = "1st_order",
    parameter mimic_fbclk_type = "gclk",
    parameter pll_fbclk_mux_1 = "glb",
    parameter pll_fbclk_mux_2 = "fb_1",
    parameter pll_m_cnt_in_src = "ph_mux_clk",
	parameter pll_vcoph_div = 1,
    parameter refclk1_frequency = "0 MHz",
    parameter pll_clkin_0_src = "clk_0",
    parameter pll_clkin_1_src = "clk_0",
    parameter pll_clk_loss_sw_en = "false",
    parameter pll_auto_clk_sw_en = "false",
    parameter pll_manu_clk_sw_en = "false", 
    parameter pll_clk_sw_dly = 0,
    parameter pll_extclk_0_cnt_src = "pll_extclk_cnt_src_vss",	
    parameter pll_extclk_1_cnt_src = "pll_extclk_cnt_src_vss"
) (
    //input
    input    refclk,
    input    refclk1,
    input    fbclk,
    input    rst,
    input    phase_en,
    input    updn,
    input    [2:0] num_phase_shifts,
    input    scanclk,
    input    [4:0] cntsel,
    input    [63:0] reconfig_to_pll,
    input    extswitch,
    input    adjpllin,
    input    cclk,
    
    //output
    output    [ number_of_clocks -1 : 0] outclk,
    output    fboutclk,
    output    locked,
    output    phase_done,
    output    [63:0]    reconfig_from_pll,
    output    activeclk,
    output    [1:0] clkbad,
	output    [7:0] phout,
	output	  [1:0] lvds_clk,
	output	  [1:0] loaden,
	output    [1:0] extclk_out,
    output    [ number_of_clocks -1 : 0] cascade_out,

    //inout
    inout zdbfbclk
);

endmodule


(* blackbox *)
module altera_std_synchronizer(clk, din, dout, reset_n);

parameter depth = 2;

input clk;
input reset_n;
input din;
output dout;

endmodule

(* blackbox *)
module altddio_in (
    datain,    // required port, DDR input data
    inclock,   // required port, input reference clock to sample data by
    inclocken, // enable data clock
    aset,      // asynchronous set
    aclr,      // asynchronous clear
    sset,      // synchronous set
    sclr,      // synchronous clear
    dataout_h, // data sampled at the rising edge of inclock
    dataout_l  // data sampled at the falling edge of inclock
);

parameter width = 1;
parameter power_up_high = "OFF";
parameter invert_input_clocks = "OFF";
parameter intended_device_family = "Stratix";
parameter lpm_type = "altddio_in";
parameter lpm_hint = "UNUSED";

input [width-1:0] datain;
input inclock;
input inclocken;
input aset;
input aclr;
input sset;
input sclr;

output [width-1:0] dataout_h;
output [width-1:0] dataout_l;

endmodule


(* blackbox *)
module altddio_out (
    datain_h,
    datain_l,
    outclock,
    outclocken,
    aset,
    aclr,
    sset,
    sclr,
    oe,
    dataout,
    oe_out
);

parameter width = 1;
parameter power_up_high = "OFF";
parameter oe_reg = "UNUSED";
parameter extend_oe_disable = "UNUSED";
parameter intended_device_family = "Stratix";
parameter invert_output = "OFF";
parameter lpm_type = "altddio_out";
parameter lpm_hint = "UNUSED";

input [width-1:0] datain_h;
input [width-1:0] datain_l;
input outclock;
input outclocken;
input aset;
input aclr;
input sset;
input sclr;
input oe;

output [width-1:0] dataout;
output [width-1:0] oe_out;

endmodule


(* blackbox *)
module altddio_bidir (
    datain_h,
    datain_l,
    inclock,
    inclocken,
    outclock,
    outclocken,
    aset,
    aclr,
    sset,
    sclr,
    oe,
    dataout_h,
    dataout_l,
    combout,
    oe_out,
    dqsundelayedout,
    padio
);

// GLOBAL PARAMETER DECLARATION
parameter width = 1; // required parameter
parameter power_up_high = "OFF";
parameter oe_reg = "UNUSED";
parameter extend_oe_disable = "UNUSED";
parameter implement_input_in_lcell = "UNUSED";
parameter invert_output = "OFF";
parameter intended_device_family = "Stratix";
parameter lpm_type = "altddio_bidir";
parameter lpm_hint = "UNUSED";

// INPUT PORT DECLARATION
input [width-1:0] datain_h;
input [width-1:0] datain_l;
input inclock;
input inclocken;
input outclock;
input outclocken;
input aset;
input aclr;
input sset;
input sclr;
input oe;

// OUTPUT PORT DECLARATION
output [width-1:0] dataout_h;
output [width-1:0] dataout_l;
output [width-1:0] combout;
output [width-1:0] oe_out;
output [width-1:0] dqsundelayedout;
// BIDIRECTIONAL PORT DECLARATION
inout  [width-1:0] padio;

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

(* blackbox *)
module cyclonev_mac(ax, ay, resulta);

parameter ax_width = 9;
parameter signed_max = "true";
parameter ay_scan_in_width = 9;
parameter signed_may = "true";
parameter result_a_width = 18;
parameter operation_mode = "M9x9";

input [ax_width-1:0] ax;
input [ay_scan_in_width-1:0] ay;
output [result_a_width-1:0] resulta;

endmodule

(* blackbox *)
module cyclone10gx_mac(ax, ay, resulta);

parameter ax_width = 18;
parameter signed_max = "true";
parameter ay_scan_in_width = 18;
parameter signed_may = "true";
parameter result_a_width = 36;
parameter operation_mode = "M18X18_FULL";

input [ax_width-1:0] ax;
input [ay_scan_in_width-1:0] ay;
output [result_a_width-1:0] resulta;

endmodule

(* blackbox *)
module cyclonev_ram_block(portaaddr, portadatain, portawe, portbaddr, portbdataout, portbre, clk0);

parameter operation_mode = "dual_port";
parameter logical_ram_name = "";
parameter port_a_address_width = 10;
parameter port_a_data_width = 10;
parameter port_a_logical_ram_depth = 1024;
parameter port_a_logical_ram_width = 10;
parameter port_a_first_address = 0;
parameter port_a_last_address = 1023;
parameter port_a_first_bit_number = 0;
parameter port_b_address_width = 10;
parameter port_b_data_width = 10;
parameter port_b_logical_ram_depth = 1024;
parameter port_b_logical_ram_width = 10;
parameter port_b_first_address = 0;
parameter port_b_last_address = 1023;
parameter port_b_first_bit_number = 0;
parameter port_b_address_clock = "clock0";
parameter port_b_read_enable_clock = "clock0";
parameter mem_init0 = "";
parameter mem_init1 = "";
parameter mem_init2 = "";
parameter mem_init3 = "";
parameter mem_init4 = "";

input [port_a_address_width-1:0] portaaddr;
input [port_b_address_width-1:0] portbaddr;
input [port_a_data_width-1:0] portadatain;
output [port_b_data_width-1:0] portbdataout;
input clk0, portawe, portbre;

endmodule

(* blackbox *)
module cyclone10gx_io_ibuf(i, ibar, dynamicterminationcontrol, o);

parameter differential_mode ="false";
parameter bus_hold = "false";
parameter simulate_z_as = "Z";
parameter lpm_type = "cyclone10gx_io_ibuf";

(* iopad_external_pin *) input i;
(* iopad_external_pin *) input ibar;
input dynamicterminationcontrol;
output o;

endmodule

(* blackbox *)
module cyclone10gx_io_obuf(i, oe, dynamicterminationcontrol, seriesterminationcontrol, parallelterminationcontrol, devoe, o, obar);

parameter open_drain_output = "false";
parameter bus_hold = "false";
parameter shift_series_termination_control = "false";
parameter sim_dynamic_termination_control_is_connected = "false";
parameter lpm_type = "cyclone10gx_io_obuf";

input i;
input oe;
input devoe;
input dynamicterminationcontrol;
input [15:0] seriesterminationcontrol;
input [15:0] parallelterminationcontrol;
(* iopad_external_pin *) output o;
(* iopad_external_pin *) output obar;

endmodule

(* blackbox *)
module cyclonev_clkena(inclk, ena, enaout, outclk);

parameter clock_type = "auto";
parameter ena_register_mode = "always enabled";
parameter lpm_type = "cyclonev_clkena";
parameter ena_register_power_up = "high";
parameter disable_mode = "low";
parameter test_syn = "high";

input inclk;
input ena;
output enaout;
output outclk;

endmodule

(* blackbox *)
module cyclone10gx_clkena(inclk, ena, enaout, outclk);

parameter clock_type = "auto";
parameter ena_register_mode = "always enabled";
parameter lpm_type = "cyclone10gx_clkena";
parameter ena_register_power_up = "high";
parameter disable_mode = "low";
parameter test_syn = "high";

input inclk;
input ena;
output enaout;
output outclk;

endmodule

// Internal interfaces
(* keep *)
module cyclonev_oscillator(oscena, clkout, clkout1);

input oscena;
output clkout;
output clkout1;

endmodule

// HPS interfaces
(* keep *)
module cyclonev_hps_interface_mpu_general_purpose(gp_in, gp_out);

input [31:0] gp_in;
output [31:0] gp_out;

endmodule
