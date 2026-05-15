//-------------------------------------------------
// IMPORTANT: This file is auto generated!!! DO NOT MODIFY BY HAND!!!
//-------------------------------------------------
// Pcounter Primitives
// Naming convention:
//   pcounter<size>_clk<trigger_type>_<reset_type>rst<reset_poloarity>_<event_function>
// size: [N | <int> ] ranges from 0 to 31, representing the number of bits. N is a parameterized design, which is supposed not be exposed to users
// trigger_type: [p|n] denotes [rising edge (posedge) | falling edge (negedge) ]
// reset_type: [a|s] denotes [ asynchronous | synchronous ]
// reset_polarity: [p|n] denotes [ active-high | active-low ]
// event_function : [ load | add | sub | sr | sl ] denotes [ load | add | substract | shift right | shift left ] on the data_i values
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with synchronous active-low reset

// Capable of load values from inputs

`default_nettype none

module pcounterN_clkp_srstn_load #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_srstn_load #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_srstn_load #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_srstn_load #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_srstn_load #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with synchronous active-low reset

// Capable of load values from inputs

`default_nettype none

module pcounterN_clkp_srstn_load_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_srstn_load_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkp_srstn_load_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_srstn_load_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkp_srstn_load_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with synchronous active-low reset

// Capable of add values from inputs

`default_nettype none

module pcounterN_clkp_srstn_add #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o + LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_srstn_add #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_srstn_add #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_srstn_add #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_srstn_add #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with synchronous active-low reset

// Capable of add values from inputs

`default_nettype none

module pcounterN_clkp_srstn_add_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o + ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_srstn_add_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkp_srstn_add_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_srstn_add_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkp_srstn_add_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with synchronous active-low reset

// Capable of subtract values from inputs

`default_nettype none

module pcounterN_clkp_srstn_sub #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o - LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_srstn_sub #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_srstn_sub #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_srstn_sub #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_srstn_sub #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with synchronous active-low reset

// Capable of subtract values from inputs

`default_nettype none

module pcounterN_clkp_srstn_sub_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o - ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_srstn_sub_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkp_srstn_sub_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_srstn_sub_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkp_srstn_sub_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with synchronous active-low reset

// Capable of shift-right values from inputs

`default_nettype none

module pcounterN_clkp_srstn_sr #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o >> LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_srstn_sr #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_srstn_sr #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_srstn_sr #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_srstn_sr #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with synchronous active-low reset

// Capable of shift-right values from inputs

`default_nettype none

module pcounterN_clkp_srstn_sr_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o >> ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_srstn_sr_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkp_srstn_sr_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_srstn_sr_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkp_srstn_sr_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with synchronous active-low reset

// Capable of shift-left values from inputs

`default_nettype none

module pcounterN_clkp_srstn_sl #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o << LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_srstn_sl #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_srstn_sl #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_srstn_sl #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_srstn_sl #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with synchronous active-low reset

// Capable of shift-left values from inputs

`default_nettype none

module pcounterN_clkp_srstn_sl_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o << ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_srstn_sl_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkp_srstn_sl_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_srstn_sl_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkp_srstn_sl_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with synchronous active-high reset

// Capable of load values from inputs

`default_nettype none

module pcounterN_clkp_srstp_load #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_srstp_load #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_srstp_load #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_srstp_load #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_srstp_load #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with synchronous active-high reset

// Capable of load values from inputs

`default_nettype none

module pcounterN_clkp_srstp_load_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_srstp_load_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkp_srstp_load_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_srstp_load_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkp_srstp_load_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with synchronous active-high reset

// Capable of add values from inputs

`default_nettype none

module pcounterN_clkp_srstp_add #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o + LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_srstp_add #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_srstp_add #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_srstp_add #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_srstp_add #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with synchronous active-high reset

// Capable of add values from inputs

`default_nettype none

module pcounterN_clkp_srstp_add_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o + ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_srstp_add_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkp_srstp_add_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_srstp_add_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkp_srstp_add_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with synchronous active-high reset

// Capable of subtract values from inputs

`default_nettype none

module pcounterN_clkp_srstp_sub #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o - LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_srstp_sub #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_srstp_sub #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_srstp_sub #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_srstp_sub #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with synchronous active-high reset

// Capable of subtract values from inputs

`default_nettype none

module pcounterN_clkp_srstp_sub_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o - ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_srstp_sub_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkp_srstp_sub_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_srstp_sub_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkp_srstp_sub_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with synchronous active-high reset

// Capable of shift-right values from inputs

`default_nettype none

module pcounterN_clkp_srstp_sr #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o >> LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_srstp_sr #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_srstp_sr #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_srstp_sr #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_srstp_sr #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with synchronous active-high reset

// Capable of shift-right values from inputs

`default_nettype none

module pcounterN_clkp_srstp_sr_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o >> ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_srstp_sr_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkp_srstp_sr_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_srstp_sr_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkp_srstp_sr_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with synchronous active-high reset

// Capable of shift-left values from inputs

`default_nettype none

module pcounterN_clkp_srstp_sl #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o << LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_srstp_sl #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_srstp_sl #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_srstp_sl #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_srstp_sl #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with synchronous active-high reset

// Capable of shift-left values from inputs

`default_nettype none

module pcounterN_clkp_srstp_sl_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o << ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_srstp_sl_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkp_srstp_sl_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_srstp_sl_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkp_srstp_sl_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with asynchronous active-low reset

// Capable of load values from inputs

`default_nettype none

module pcounterN_clkp_arstn_load #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i or negedge rst_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_arstn_load #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_arstn_load #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_arstn_load #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_arstn_load #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with asynchronous active-low reset

// Capable of load values from inputs

`default_nettype none

module pcounterN_clkp_arstn_load_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i or negedge rst_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_arstn_load_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkp_arstn_load_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_arstn_load_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkp_arstn_load_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with asynchronous active-low reset

// Capable of add values from inputs

`default_nettype none

module pcounterN_clkp_arstn_add #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i or negedge rst_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o + LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_arstn_add #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_arstn_add #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_arstn_add #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_arstn_add #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with asynchronous active-low reset

// Capable of add values from inputs

`default_nettype none

module pcounterN_clkp_arstn_add_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i or negedge rst_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o + ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_arstn_add_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkp_arstn_add_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_arstn_add_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkp_arstn_add_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with asynchronous active-low reset

// Capable of subtract values from inputs

`default_nettype none

module pcounterN_clkp_arstn_sub #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i or negedge rst_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o - LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_arstn_sub #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_arstn_sub #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_arstn_sub #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_arstn_sub #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with asynchronous active-low reset

// Capable of subtract values from inputs

`default_nettype none

module pcounterN_clkp_arstn_sub_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i or negedge rst_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o - ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_arstn_sub_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkp_arstn_sub_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_arstn_sub_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkp_arstn_sub_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with asynchronous active-low reset

// Capable of shift-right values from inputs

`default_nettype none

module pcounterN_clkp_arstn_sr #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i or negedge rst_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o >> LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_arstn_sr #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_arstn_sr #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_arstn_sr #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_arstn_sr #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with asynchronous active-low reset

// Capable of shift-right values from inputs

`default_nettype none

module pcounterN_clkp_arstn_sr_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i or negedge rst_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o >> ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_arstn_sr_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkp_arstn_sr_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_arstn_sr_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkp_arstn_sr_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with asynchronous active-low reset

// Capable of shift-left values from inputs

`default_nettype none

module pcounterN_clkp_arstn_sl #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i or negedge rst_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o << LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_arstn_sl #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_arstn_sl #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_arstn_sl #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_arstn_sl #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with asynchronous active-low reset

// Capable of shift-left values from inputs

`default_nettype none

module pcounterN_clkp_arstn_sl_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i or negedge rst_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o << ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_arstn_sl_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkp_arstn_sl_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_arstn_sl_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkp_arstn_sl_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with asynchronous active-high reset

// Capable of load values from inputs

`default_nettype none

module pcounterN_clkp_arstp_load #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i or posedge rst_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_arstp_load #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_arstp_load #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_arstp_load #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_arstp_load #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with asynchronous active-high reset

// Capable of load values from inputs

`default_nettype none

module pcounterN_clkp_arstp_load_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i or posedge rst_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_arstp_load_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkp_arstp_load_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_arstp_load_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkp_arstp_load_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with asynchronous active-high reset

// Capable of add values from inputs

`default_nettype none

module pcounterN_clkp_arstp_add #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i or posedge rst_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o + LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_arstp_add #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_arstp_add #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_arstp_add #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_arstp_add #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with asynchronous active-high reset

// Capable of add values from inputs

`default_nettype none

module pcounterN_clkp_arstp_add_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i or posedge rst_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o + ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_arstp_add_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkp_arstp_add_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_arstp_add_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkp_arstp_add_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with asynchronous active-high reset

// Capable of subtract values from inputs

`default_nettype none

module pcounterN_clkp_arstp_sub #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i or posedge rst_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o - LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_arstp_sub #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_arstp_sub #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_arstp_sub #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_arstp_sub #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with asynchronous active-high reset

// Capable of subtract values from inputs

`default_nettype none

module pcounterN_clkp_arstp_sub_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i or posedge rst_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o - ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_arstp_sub_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkp_arstp_sub_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_arstp_sub_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkp_arstp_sub_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with asynchronous active-high reset

// Capable of shift-right values from inputs

`default_nettype none

module pcounterN_clkp_arstp_sr #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i or posedge rst_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o >> LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_arstp_sr #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_arstp_sr #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_arstp_sr #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_arstp_sr #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with asynchronous active-high reset

// Capable of shift-right values from inputs

`default_nettype none

module pcounterN_clkp_arstp_sr_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i or posedge rst_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o >> ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_arstp_sr_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkp_arstp_sr_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_arstp_sr_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkp_arstp_sr_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with asynchronous active-high reset

// Capable of shift-left values from inputs

`default_nettype none

module pcounterN_clkp_arstp_sl #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i or posedge rst_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o << LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_arstp_sl #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_arstp_sl #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_arstp_sl #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkp_arstp_sl #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by rising edge clock

// with asynchronous active-high reset

// Capable of shift-left values from inputs

`default_nettype none

module pcounterN_clkp_arstp_sl_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(posedge clk_i or posedge rst_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o << ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkp_arstp_sl_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkp_arstp_sl_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkp_arstp_sl_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkp_arstp_sl_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with synchronous active-low reset

// Capable of load values from inputs

`default_nettype none

module pcounterN_clkn_srstn_load #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_srstn_load #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_srstn_load #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_srstn_load #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_srstn_load #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with synchronous active-low reset

// Capable of load values from inputs

`default_nettype none

module pcounterN_clkn_srstn_load_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_srstn_load_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkn_srstn_load_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_srstn_load_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkn_srstn_load_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with synchronous active-low reset

// Capable of add values from inputs

`default_nettype none

module pcounterN_clkn_srstn_add #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o + LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_srstn_add #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_srstn_add #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_srstn_add #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_srstn_add #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with synchronous active-low reset

// Capable of add values from inputs

`default_nettype none

module pcounterN_clkn_srstn_add_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o + ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_srstn_add_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkn_srstn_add_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_srstn_add_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkn_srstn_add_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with synchronous active-low reset

// Capable of subtract values from inputs

`default_nettype none

module pcounterN_clkn_srstn_sub #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o - LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_srstn_sub #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_srstn_sub #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_srstn_sub #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_srstn_sub #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with synchronous active-low reset

// Capable of subtract values from inputs

`default_nettype none

module pcounterN_clkn_srstn_sub_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o - ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_srstn_sub_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkn_srstn_sub_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_srstn_sub_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkn_srstn_sub_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with synchronous active-low reset

// Capable of shift-right values from inputs

`default_nettype none

module pcounterN_clkn_srstn_sr #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o >> LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_srstn_sr #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_srstn_sr #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_srstn_sr #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_srstn_sr #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with synchronous active-low reset

// Capable of shift-right values from inputs

`default_nettype none

module pcounterN_clkn_srstn_sr_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o >> ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_srstn_sr_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkn_srstn_sr_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_srstn_sr_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkn_srstn_sr_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with synchronous active-low reset

// Capable of shift-left values from inputs

`default_nettype none

module pcounterN_clkn_srstn_sl #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o << LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_srstn_sl #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_srstn_sl #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_srstn_sl #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_srstn_sl #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with synchronous active-low reset

// Capable of shift-left values from inputs

`default_nettype none

module pcounterN_clkn_srstn_sl_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o << ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_srstn_sl_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkn_srstn_sl_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_srstn_sl_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkn_srstn_sl_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with synchronous active-high reset

// Capable of load values from inputs

`default_nettype none

module pcounterN_clkn_srstp_load #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_srstp_load #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_srstp_load #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_srstp_load #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_srstp_load #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with synchronous active-high reset

// Capable of load values from inputs

`default_nettype none

module pcounterN_clkn_srstp_load_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_srstp_load_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkn_srstp_load_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_srstp_load_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkn_srstp_load_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with synchronous active-high reset

// Capable of add values from inputs

`default_nettype none

module pcounterN_clkn_srstp_add #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o + LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_srstp_add #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_srstp_add #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_srstp_add #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_srstp_add #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with synchronous active-high reset

// Capable of add values from inputs

`default_nettype none

module pcounterN_clkn_srstp_add_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o + ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_srstp_add_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkn_srstp_add_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_srstp_add_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkn_srstp_add_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with synchronous active-high reset

// Capable of subtract values from inputs

`default_nettype none

module pcounterN_clkn_srstp_sub #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o - LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_srstp_sub #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_srstp_sub #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_srstp_sub #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_srstp_sub #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with synchronous active-high reset

// Capable of subtract values from inputs

`default_nettype none

module pcounterN_clkn_srstp_sub_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o - ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_srstp_sub_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkn_srstp_sub_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_srstp_sub_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkn_srstp_sub_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with synchronous active-high reset

// Capable of shift-right values from inputs

`default_nettype none

module pcounterN_clkn_srstp_sr #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o >> LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_srstp_sr #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_srstp_sr #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_srstp_sr #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_srstp_sr #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with synchronous active-high reset

// Capable of shift-right values from inputs

`default_nettype none

module pcounterN_clkn_srstp_sr_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o >> ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_srstp_sr_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkn_srstp_sr_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_srstp_sr_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkn_srstp_sr_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with synchronous active-high reset

// Capable of shift-left values from inputs

`default_nettype none

module pcounterN_clkn_srstp_sl #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o << LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_srstp_sl #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_srstp_sl #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_srstp_sl #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_srstp_sl #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with synchronous active-high reset

// Capable of shift-left values from inputs

`default_nettype none

module pcounterN_clkn_srstp_sl_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o << ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_srstp_sl_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkn_srstp_sl_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_srstp_sl_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkn_srstp_sl_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with asynchronous active-low reset

// Capable of load values from inputs

`default_nettype none

module pcounterN_clkn_arstn_load #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i or negedge rst_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_arstn_load #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_arstn_load #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_arstn_load #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_arstn_load #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with asynchronous active-low reset

// Capable of load values from inputs

`default_nettype none

module pcounterN_clkn_arstn_load_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i or negedge rst_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_arstn_load_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkn_arstn_load_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_arstn_load_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkn_arstn_load_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with asynchronous active-low reset

// Capable of add values from inputs

`default_nettype none

module pcounterN_clkn_arstn_add #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i or negedge rst_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o + LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_arstn_add #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_arstn_add #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_arstn_add #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_arstn_add #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with asynchronous active-low reset

// Capable of add values from inputs

`default_nettype none

module pcounterN_clkn_arstn_add_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i or negedge rst_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o + ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_arstn_add_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkn_arstn_add_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_arstn_add_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkn_arstn_add_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with asynchronous active-low reset

// Capable of subtract values from inputs

`default_nettype none

module pcounterN_clkn_arstn_sub #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i or negedge rst_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o - LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_arstn_sub #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_arstn_sub #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_arstn_sub #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_arstn_sub #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with asynchronous active-low reset

// Capable of subtract values from inputs

`default_nettype none

module pcounterN_clkn_arstn_sub_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i or negedge rst_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o - ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_arstn_sub_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkn_arstn_sub_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_arstn_sub_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkn_arstn_sub_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with asynchronous active-low reset

// Capable of shift-right values from inputs

`default_nettype none

module pcounterN_clkn_arstn_sr #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i or negedge rst_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o >> LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_arstn_sr #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_arstn_sr #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_arstn_sr #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_arstn_sr #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with asynchronous active-low reset

// Capable of shift-right values from inputs

`default_nettype none

module pcounterN_clkn_arstn_sr_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i or negedge rst_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o >> ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_arstn_sr_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkn_arstn_sr_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_arstn_sr_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkn_arstn_sr_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with asynchronous active-low reset

// Capable of shift-left values from inputs

`default_nettype none

module pcounterN_clkn_arstn_sl #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i or negedge rst_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o << LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_arstn_sl #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_arstn_sl #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_arstn_sl #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_arstn_sl #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with asynchronous active-low reset

// Capable of shift-left values from inputs

`default_nettype none

module pcounterN_clkn_arstn_sl_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i or negedge rst_i) 
  begin
    if (~rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o << ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_arstn_sl_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkn_arstn_sl_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_arstn_sl_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkn_arstn_sl_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with asynchronous active-high reset

// Capable of load values from inputs

`default_nettype none

module pcounterN_clkn_arstp_load #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i or posedge rst_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_arstp_load #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_arstp_load #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_arstp_load #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_arstp_load #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with asynchronous active-high reset

// Capable of load values from inputs

`default_nettype none

module pcounterN_clkn_arstp_load_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i or posedge rst_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_arstp_load_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkn_arstp_load_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_arstp_load_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkn_arstp_load_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with asynchronous active-high reset

// Capable of add values from inputs

`default_nettype none

module pcounterN_clkn_arstp_add #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i or posedge rst_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o + LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_arstp_add #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_arstp_add #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_arstp_add #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_arstp_add #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with asynchronous active-high reset

// Capable of add values from inputs

`default_nettype none

module pcounterN_clkn_arstp_add_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i or posedge rst_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o + ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_arstp_add_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkn_arstp_add_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_arstp_add_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkn_arstp_add_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with asynchronous active-high reset

// Capable of subtract values from inputs

`default_nettype none

module pcounterN_clkn_arstp_sub #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i or posedge rst_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o - LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_arstp_sub #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_arstp_sub #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_arstp_sub #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_arstp_sub #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with asynchronous active-high reset

// Capable of subtract values from inputs

`default_nettype none

module pcounterN_clkn_arstp_sub_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i or posedge rst_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o - ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_arstp_sub_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkn_arstp_sub_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_arstp_sub_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkn_arstp_sub_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with asynchronous active-high reset

// Capable of shift-right values from inputs

`default_nettype none

module pcounterN_clkn_arstp_sr #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i or posedge rst_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o >> LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_arstp_sr #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_arstp_sr #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_arstp_sr #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_arstp_sr #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with asynchronous active-high reset

// Capable of shift-right values from inputs

`default_nettype none

module pcounterN_clkn_arstp_sr_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i or posedge rst_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o >> ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_arstp_sr_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkn_arstp_sr_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_arstp_sr_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkn_arstp_sr_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with asynchronous active-high reset

// Capable of shift-left values from inputs

`default_nettype none

module pcounterN_clkn_arstp_sl #(
  parameter integer DATA_WIDTH = 32,
  parameter [0 : DATA_WIDTH - 1] LOAD_VAL = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH0_REF = {DATA_WIDTH{1'b0}},
  parameter [0 : DATA_WIDTH - 1] MATCH1_REF = {DATA_WIDTH{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i or posedge rst_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o << LOAD_VAL;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == MATCH0_REF) ? 1 : 0;
  assign match1_o = (q_o == MATCH1_REF) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_arstp_sl #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 31] LOAD_VAL = {32{1'b0}},
  parameter [0 : 31] MATCH0_REF = {32{1'b0}},
  parameter [0 : 31] MATCH1_REF = {32{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_arstp_sl #(
    .DATA_WIDTH(32),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_arstp_sl #(
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0,
  parameter [0 : 15] LOAD_VAL = {16{1'b0}},
  parameter [0 : 15] MATCH0_REF = {16{1'b0}},
  parameter [0 : 15] MATCH1_REF = {16{1'b0}}
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  output match0_o,
  output match1_o,
  output zero_o
);
  pcounterN_clkn_arstp_sl #(
    .DATA_WIDTH(16),
    .LOAD_VAL(LOAD_VAL),
    .MATCH0_REF(MATCH0_REF),
    .MATCH1_REF(MATCH1_REF)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o)
  );
endmodule
`default_nettype wire
//-------------------------------------------------

// Template of Programmable counter to be counting up or down as well as paused

// triggered by falling edge clock

// with asynchronous active-high reset

// Capable of shift-left values from inputs

`default_nettype none

module pcounterN_clkn_arstp_sl_ccb #(
  parameter integer DATA_WIDTH = 32
)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : DATA_WIDTH - 1] ccb_match0_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_match1_ref_i,
  input [0 : DATA_WIDTH - 1] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : DATA_WIDTH - 1] q_o
);
  reg [0 : DATA_WIDTH - 1] q_o;
  always@(negedge clk_i or posedge rst_i) 
  begin
    if (rst_i)    //Set Counter to Zero
      q_o <= 0;
    else if(event_i)
      q_o <= q_o << ccb_load_val_i;
    else if (~enable_i)
      q_o <= q_o;  // pause
    else if(up_down_i)        //count down
      q_o <= q_o - 1;
    else            //count up
      q_o <= q_o + 1;
  end
  assign zero_o = (q_o == 0) ? 1 : 0;
  assign match0_o = (q_o == ccb_match0_ref_i) ? 1 : 0;
  assign match1_o = (q_o == ccb_match1_ref_i) ? 1 : 0;
endmodule
`default_nettype wire
`default_nettype none

module pcounter32_clkn_arstp_sl_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 31] ccb_match0_ref_i,
  input [0 : 31] ccb_match1_ref_i,
  input [0 : 31] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 31] q_o
);
  pcounterN_clkn_arstp_sl_ccb #(
    .DATA_WIDTH(32)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
`default_nettype none

module pcounter16_clkn_arstp_sl_ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0,
  parameter FPGA_LOC_Y = 0,
  parameter FPGA_LOC_Z = 0)(
  input clk_i,
  input rst_i,
  input up_down_i,
  input event_i,
  input enable_i,
  input [0 : 15] ccb_match0_ref_i,
  input [0 : 15] ccb_match1_ref_i,
  input [0 : 15] ccb_load_val_i,
  output match0_o,
  output match1_o,
  output zero_o,
  output [0 : 15] q_o
);
  pcounterN_clkn_arstp_sl_ccb #(
    .DATA_WIDTH(16)
  ) core (
    .clk_i(clk_i),
    .rst_i(rst_i),
    .up_down_i(up_down_i),
    .event_i(event_i),
    .enable_i(enable_i),
    .ccb_load_val_i(ccb_load_val_i),
    .ccb_match0_ref_i(ccb_match0_ref_i),
    .ccb_match1_ref_i(ccb_match1_ref_i),
    .match0_o(match0_o),
    .match1_o(match1_o),
    .zero_o(zero_o),
    .q_o(q_o)
  );
endmodule
`default_nettype wire
