//-------------------------------------------------
// Counter Configuration Block (CCB) Primitives
//-------------------------------------------------
`default_nettype none

module ccb # (
  // Location constraints
  parameter FPGA_LOC_X = 0, 
  parameter FPGA_LOC_Y = 0, 
  parameter FPGA_LOC_Z = 0, 
  // Event0 triggered instructions
  parameter [0:9] EVENT0_INST0 = `NA,
  parameter [0:9] EVENT0_INST1 = `NA,
  parameter [0:9] EVENT0_INST2 = `NA,
  parameter [0:9] EVENT0_INST3 = `NA,
  parameter [0:9] EVENT0_INST4 = `NA,
  parameter [0:9] EVENT0_INST5 = `NA,
  parameter [0:9] EVENT0_INST6 = `NA,
  parameter [0:9] EVENT0_INST7 = `NA,
  // Event1 triggered instructions
  parameter [0:9] EVENT1_INST0 = `NA,
  parameter [0:9] EVENT1_INST1 = `NA,
  parameter [0:9] EVENT1_INST2 = `NA,
  parameter [0:9] EVENT1_INST3 = `NA,
  parameter [0:9] EVENT1_INST4 = `NA,
  parameter [0:9] EVENT1_INST5 = `NA,
  parameter [0:9] EVENT1_INST6 = `NA,
  parameter [0:9] EVENT1_INST7 = `NA,
  // Event2 triggered instructions
  parameter [0:9] EVENT2_INST0 = `NA,
  parameter [0:9] EVENT2_INST1 = `NA,
  parameter [0:9] EVENT2_INST2 = `NA,
  parameter [0:9] EVENT2_INST3 = `NA,
  parameter [0:9] EVENT2_INST4 = `NA,
  parameter [0:9] EVENT2_INST5 = `NA,
  parameter [0:9] EVENT2_INST6 = `NA,
  parameter [0:9] EVENT2_INST7 = `NA,
  // Event3 triggered instructions
  parameter [0:9] EVENT3_INST0 = `NA,
  parameter [0:9] EVENT3_INST1 = `NA,
  parameter [0:9] EVENT3_INST2 = `NA,
  parameter [0:9] EVENT3_INST3 = `NA,
  parameter [0:9] EVENT3_INST4 = `NA,
  parameter [0:9] EVENT3_INST5 = `NA,
  parameter [0:9] EVENT3_INST6 = `NA,
  parameter [0:9] EVENT3_INST7 = `NA,
  // Initial register values, R0-R3
  parameter [0:31] R0 = {32{1'b0}}, 
  parameter [0:31] R1 = {32{1'b0}}, 
  parameter [0:31] R2 = {32{1'b0}}, 
  parameter [0:31] R3 = {32{1'b0}}, 
  // FIFO initial values
  parameter [0:31] FIFO_INIT0 = {32{1'b0}}, 
  parameter [0:31] FIFO_INIT1 = {32{1'b0}}, 
  parameter [0:31] FIFO_INIT2 = {32{1'b0}}, 
  parameter [0:31] FIFO_INIT3 = {32{1'b0}},
  // PCNT initial values
  parameter [0:31] LOAD_VAL_PCNT0 = {32{1'b0}},
  parameter [0:31] LOAD_VAL_PCNT1 = {32{1'b0}},
  parameter [0:31] LOAD_VAL_PCNT2 = {32{1'b0}},
  parameter [0:31] MATCH0_REF_PCNT0 = {32{1'b0}},
  parameter [0:31] MATCH0_REF_PCNT1 = {32{1'b0}},
  parameter [0:31] MATCH0_REF_PCNT2 = {32{1'b0}},
  parameter [0:31] MATCH1_REF_PCNT0 = {32{1'b0}},
  parameter [0:31] MATCH1_REF_PCNT1 = {32{1'b0}},
  parameter [0:31] MATCH1_REF_PCNT2 = {32{1'b0}}
)(
  input ccb_clk_i, 
  input ccb_rst_ni, 
  input [0:3] ccb_event_i,
  input [0:5] pcnt_event_i,
  output [0:31] match0_ref0_o,
  output [0:31] match1_ref0_o,
  output [0:31] load_val0_o,
  output [0:31] match0_ref1_o,
  output [0:31] match1_ref1_o,
  output [0:31] load_val1_o,
  output [0:31] match0_ref2_o,
  output [0:31] match1_ref2_o,
  output [0:31] load_val2_o
  
);


// Dummy
assign match0_ref0_o = 0;
assign match1_ref0_o = 0;
assign load_val0_o = 0;

assign match0_ref1_o = 0;
assign match1_ref1_o = 0;
assign load_val1_o = 0;

assign match0_ref2_o = 0;
assign match1_ref2_o = 0;
assign load_val2_o = 0;


endmodule

`default_nettype wire
