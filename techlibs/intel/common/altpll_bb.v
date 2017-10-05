/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */
/* No clearbox model */
`ifdef NO_CLEARBOX
(* blackbox *)
module altpll
  ( inclk,
    fbin,
    pllena,
    clkswitch,
    areset,
    pfdena,
    clkena,
    extclkena,
    scanclk,
    scanaclr,
    scanclkena,
    scanread,
    scanwrite,
    scandata,
    phasecounterselect,
    phaseupdown,
    phasestep,
    configupdate,
    fbmimicbidir,
    clk,
    extclk,
    clkbad,
    enable0,
    enable1,
    activeclock,
    clkloss,
    locked,
    scandataout,
    scandone,
    sclkout0,
    sclkout1,
    phasedone,
    vcooverrange,
    vcounderrange,
    fbout,
    fref,
    icdrclk,
    c0,
    c1,
    c2,
    c3,
    c4);

   parameter   intended_device_family    = "MAX 10";
   parameter   operation_mode            = "NORMAL";
   parameter   pll_type                  = "AUTO";
   parameter   qualify_conf_done         = "OFF";
   parameter   compensate_clock          = "CLK0";
   parameter   scan_chain                = "LONG";
   parameter   primary_clock             = "inclk0";
   parameter   inclk0_input_frequency    = 1000;
   parameter   inclk1_input_frequency    = 0;
   parameter   gate_lock_signal          = "NO";
   parameter   gate_lock_counter         = 0;
   parameter   lock_high                 = 1;
   parameter   lock_low                  = 0;
   parameter   valid_lock_multiplier     = 1;
   parameter   invalid_lock_multiplier   = 5;
   parameter   switch_over_type          = "AUTO";
   parameter   switch_over_on_lossclk    = "OFF" ;
   parameter   switch_over_on_gated_lock = "OFF" ;
   parameter   enable_switch_over_counter = "OFF";
   parameter   switch_over_counter       = 0;
   parameter   feedback_source           = "EXTCLK0" ;
   parameter   bandwidth                 = 0;
   parameter   bandwidth_type            = "UNUSED";
   parameter   lpm_hint                  = "UNUSED";
   parameter   spread_frequency          = 0;
   parameter   down_spread               = "0.0";
   parameter   self_reset_on_gated_loss_lock = "OFF";
   parameter   self_reset_on_loss_lock = "OFF";
   parameter   lock_window_ui           = "0.05";
   parameter   width_clock              = 6;
   parameter   width_phasecounterselect = 4;
   parameter   charge_pump_current_bits = 9999;
   parameter   loop_filter_c_bits = 9999;
   parameter   loop_filter_r_bits = 9999;
   parameter   scan_chain_mif_file = "UNUSED";
   parameter   clk9_multiply_by        = 1;
   parameter   clk8_multiply_by        = 1;
   parameter   clk7_multiply_by        = 1;
   parameter   clk6_multiply_by        = 1;
   parameter   clk5_multiply_by        = 1;
   parameter   clk4_multiply_by        = 1;
   parameter   clk3_multiply_by        = 1;
   parameter   clk2_multiply_by        = 1;
   parameter   clk1_multiply_by        = 1;
   parameter   clk0_multiply_by        = 1;
   parameter   clk9_divide_by          = 1;
   parameter   clk8_divide_by          = 1;
   parameter   clk7_divide_by          = 1;
   parameter   clk6_divide_by          = 1;
   parameter   clk5_divide_by          = 1;
   parameter   clk4_divide_by          = 1;
   parameter   clk3_divide_by          = 1;
   parameter   clk2_divide_by          = 1;
   parameter   clk1_divide_by          = 1;
   parameter   clk0_divide_by          = 1;
   parameter   clk9_phase_shift        = "0";
   parameter   clk8_phase_shift        = "0";
   parameter   clk7_phase_shift        = "0";
   parameter   clk6_phase_shift        = "0";
   parameter   clk5_phase_shift        = "0";
   parameter   clk4_phase_shift        = "0";
   parameter   clk3_phase_shift        = "0";
   parameter   clk2_phase_shift        = "0";
   parameter   clk1_phase_shift        = "0";
   parameter   clk0_phase_shift        = "0";

   parameter   clk9_duty_cycle         = 50;
   parameter   clk8_duty_cycle         = 50;
   parameter   clk7_duty_cycle         = 50;
   parameter   clk6_duty_cycle         = 50;
   parameter   clk5_duty_cycle         = 50;
   parameter   clk4_duty_cycle         = 50;
   parameter   clk3_duty_cycle         = 50;
   parameter   clk2_duty_cycle         = 50;
   parameter   clk1_duty_cycle         = 50;
   parameter   clk0_duty_cycle         = 50;

   parameter   clk9_use_even_counter_mode    = "OFF";
   parameter   clk8_use_even_counter_mode    = "OFF";
   parameter   clk7_use_even_counter_mode    = "OFF";
   parameter   clk6_use_even_counter_mode    = "OFF";
   parameter   clk5_use_even_counter_mode    = "OFF";
   parameter   clk4_use_even_counter_mode    = "OFF";
   parameter   clk3_use_even_counter_mode    = "OFF";
   parameter   clk2_use_even_counter_mode    = "OFF";
   parameter   clk1_use_even_counter_mode    = "OFF";
   parameter   clk0_use_even_counter_mode    = "OFF";
   parameter   clk9_use_even_counter_value   = "OFF";
   parameter   clk8_use_even_counter_value   = "OFF";
   parameter   clk7_use_even_counter_value   = "OFF";
   parameter   clk6_use_even_counter_value   = "OFF";
   parameter   clk5_use_even_counter_value   = "OFF";
   parameter   clk4_use_even_counter_value   = "OFF";
   parameter   clk3_use_even_counter_value   = "OFF";
   parameter   clk2_use_even_counter_value   = "OFF";
   parameter   clk1_use_even_counter_value   = "OFF";
   parameter   clk0_use_even_counter_value   = "OFF";

   parameter   clk2_output_frequency   = 0;
   parameter   clk1_output_frequency   = 0;
   parameter   clk0_output_frequency   = 0;

   parameter   vco_min             = 0;
   parameter   vco_max             = 0;
   parameter   vco_center          = 0;
   parameter   pfd_min             = 0;
   parameter   pfd_max             = 0;
   parameter   m_initial           = 1;
   parameter   m                   = 0;
   parameter   n                   = 1;
   parameter   m2                  = 1;
   parameter   n2                  = 1;
   parameter   ss                  = 0;
   parameter   l0_high             = 1;
   parameter   l1_high             = 1;
   parameter   g0_high             = 1;
   parameter   g1_high             = 1;
   parameter   g2_high             = 1;
   parameter   g3_high             = 1;
   parameter   e0_high             = 1;
   parameter   e1_high             = 1;
   parameter   e2_high             = 1;
   parameter   e3_high             = 1;
   parameter   l0_low              = 1;
   parameter   l1_low              = 1;
   parameter   g0_low              = 1;
   parameter   g1_low              = 1;
   parameter   g2_low              = 1;
   parameter   g3_low              = 1;
   parameter   e0_low              = 1;
   parameter   e1_low              = 1;
   parameter   e2_low              = 1;
   parameter   e3_low              = 1;
   parameter   l0_initial          = 1;
   parameter   l1_initial          = 1;
   parameter   g0_initial          = 1;
   parameter   g1_initial          = 1;
   parameter   g2_initial          = 1;
   parameter   g3_initial          = 1;
   parameter   e0_initial          = 1;
   parameter   e1_initial          = 1;
   parameter   e2_initial          = 1;
   parameter   e3_initial          = 1;
   parameter   l0_mode             = "bypass";
   parameter   l1_mode             = "bypass";
   parameter   g0_mode             = "bypass";
   parameter   g1_mode             = "bypass";
   parameter   g2_mode             = "bypass";
   parameter   g3_mode             = "bypass";
   parameter   e0_mode             = "bypass";
   parameter   e1_mode             = "bypass";
   parameter   e2_mode             = "bypass";
   parameter   e3_mode             = "bypass";
   parameter   l0_ph               = 0;
   parameter   l1_ph               = 0;
   parameter   g0_ph               = 0;
   parameter   g1_ph               = 0;
   parameter   g2_ph               = 0;
   parameter   g3_ph               = 0;
   parameter   e0_ph               = 0;
   parameter   e1_ph               = 0;
   parameter   e2_ph               = 0;
   parameter   e3_ph               = 0;
   parameter   m_ph                = 0;
   parameter   l0_time_delay       = 0;
   parameter   l1_time_delay       = 0;
   parameter   g0_time_delay       = 0;
   parameter   g1_time_delay       = 0;
   parameter   g2_time_delay       = 0;
   parameter   g3_time_delay       = 0;
   parameter   e0_time_delay       = 0;
   parameter   e1_time_delay       = 0;
   parameter   e2_time_delay       = 0;
   parameter   e3_time_delay       = 0;
   parameter   m_time_delay        = 0;
   parameter   n_time_delay        = 0;
   parameter   extclk3_counter     = "e3" ;
   parameter   extclk2_counter     = "e2" ;
   parameter   extclk1_counter     = "e1" ;
   parameter   extclk0_counter     = "e0" ;
   parameter   clk9_counter        = "c9" ;
   parameter   clk8_counter        = "c8" ;
   parameter   clk7_counter        = "c7" ;
   parameter   clk6_counter        = "c6" ;
   parameter   clk5_counter        = "l1" ;
   parameter   clk4_counter        = "l0" ;
   parameter   clk3_counter        = "g3" ;
   parameter   clk2_counter        = "g2" ;
   parameter   clk1_counter        = "g1" ;
   parameter   clk0_counter        = "g0" ;
   parameter   enable0_counter     = "l0";
   parameter   enable1_counter     = "l0";
   parameter   charge_pump_current = 2;
   parameter   loop_filter_r       = "1.0";
   parameter   loop_filter_c       = 5;
   parameter   vco_post_scale      = 0;
   parameter   vco_frequency_control = "AUTO";
   parameter   vco_phase_shift_step = 0;
   parameter   lpm_type            = "altpll";

   parameter port_clkena0 = "PORT_CONNECTIVITY";
   parameter port_clkena1 = "PORT_CONNECTIVITY";
   parameter port_clkena2 = "PORT_CONNECTIVITY";
   parameter port_clkena3 = "PORT_CONNECTIVITY";
   parameter port_clkena4 = "PORT_CONNECTIVITY";
   parameter port_clkena5 = "PORT_CONNECTIVITY";
   parameter port_extclkena0 = "PORT_CONNECTIVITY";
   parameter port_extclkena1 = "PORT_CONNECTIVITY";
   parameter port_extclkena2 = "PORT_CONNECTIVITY";
   parameter port_extclkena3 = "PORT_CONNECTIVITY";
   parameter port_extclk0 = "PORT_CONNECTIVITY";
   parameter port_extclk1 = "PORT_CONNECTIVITY";
   parameter port_extclk2 = "PORT_CONNECTIVITY";
   parameter port_extclk3 = "PORT_CONNECTIVITY";
   parameter port_clk0 = "PORT_CONNECTIVITY";
   parameter port_clk1 = "PORT_CONNECTIVITY";
   parameter port_clk2 = "PORT_CONNECTIVITY";
   parameter port_clk3 = "PORT_CONNECTIVITY";
   parameter port_clk4 = "PORT_CONNECTIVITY";
   parameter port_clk5 = "PORT_CONNECTIVITY";
   parameter port_clk6 = "PORT_CONNECTIVITY";
   parameter port_clk7 = "PORT_CONNECTIVITY";
   parameter port_clk8 = "PORT_CONNECTIVITY";
   parameter port_clk9 = "PORT_CONNECTIVITY";
   parameter port_scandata = "PORT_CONNECTIVITY";
   parameter port_scandataout = "PORT_CONNECTIVITY";
   parameter port_scandone = "PORT_CONNECTIVITY";
   parameter port_sclkout1 = "PORT_CONNECTIVITY";
   parameter port_sclkout0 = "PORT_CONNECTIVITY";
   parameter port_clkbad0 = "PORT_CONNECTIVITY";
   parameter port_clkbad1 = "PORT_CONNECTIVITY";
   parameter port_activeclock = "PORT_CONNECTIVITY";
   parameter port_clkloss = "PORT_CONNECTIVITY";
   parameter port_inclk1 = "PORT_CONNECTIVITY";
   parameter port_inclk0 = "PORT_CONNECTIVITY";
   parameter port_fbin = "PORT_CONNECTIVITY";
   parameter port_fbout = "PORT_CONNECTIVITY";
   parameter port_pllena = "PORT_CONNECTIVITY";
   parameter port_clkswitch = "PORT_CONNECTIVITY";
   parameter port_areset = "PORT_CONNECTIVITY";
   parameter port_pfdena = "PORT_CONNECTIVITY";
   parameter port_scanclk = "PORT_CONNECTIVITY";
   parameter port_scanaclr = "PORT_CONNECTIVITY";
   parameter port_scanread = "PORT_CONNECTIVITY";
   parameter port_scanwrite = "PORT_CONNECTIVITY";
   parameter port_enable0 = "PORT_CONNECTIVITY";
   parameter port_enable1 = "PORT_CONNECTIVITY";
   parameter port_locked = "PORT_CONNECTIVITY";
   parameter port_configupdate = "PORT_CONNECTIVITY";
   parameter port_phasecounterselect = "PORT_CONNECTIVITY";
   parameter port_phasedone = "PORT_CONNECTIVITY";
   parameter port_phasestep = "PORT_CONNECTIVITY";
   parameter port_phaseupdown = "PORT_CONNECTIVITY";
   parameter port_vcooverrange = "PORT_CONNECTIVITY";
   parameter port_vcounderrange = "PORT_CONNECTIVITY";
   parameter port_scanclkena = "PORT_CONNECTIVITY";
   parameter using_fbmimicbidir_port = "ON";

   input [1:0] inclk;
   input       fbin;
   input       pllena;
   input       clkswitch;
   input       areset;
   input       pfdena;
   input       clkena;
   input       extclkena;
   input       scanclk;
   input       scanaclr;
   input       scanclkena;
   input       scanread;
   input       scanwrite;
   input       scandata;
   input       phasecounterselect;
   input       phaseupdown;
   input       phasestep;
   input       configupdate;
   inout       fbmimicbidir;


   output [width_clock-1:0] clk;
   output [3:0]             extclk;
   output [1:0]             clkbad;
   output                   enable0;
   output                   enable1;
   output                   activeclock;
   output                   clkloss;
   output                   locked;
   output                   scandataout;
   output                   scandone;
   output                   sclkout0;
   output                   sclkout1;
   output                   phasedone;
   output                   vcooverrange;
   output                   vcounderrange;
   output                   fbout;
   output                   fref;
   output                   icdrclk;
   output                   c0, c1, c2, c3, c4;

endmodule // altpll
`endif
