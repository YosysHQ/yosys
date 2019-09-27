`timescale 1ns/10ps

module svinterface_at_top_wrapper(
  input logic clk,
  input logic rst,
  output logic [21:0] outOther,
  input logic [1:0] sig,
  output logic [1:0] sig_out,
  input logic flip,
  output logic [15:0] passThrough,

    input logic interfaceInstanceAtTop_setting,
    output logic [2:0] interfaceInstanceAtTop_other_setting,
    output logic [1:0] interfaceInstanceAtTop_mysig_out,
    output logic [15:0] interfaceInstanceAtTop_passThrough,
  );


  TopModule u_dut (
    .clk(clk),
    .rst(rst),
    .outOther(outOther),
    .sig(sig),
    .flip(flip),
    .passThrough(passThrough),
    .\interfaceInstanceAtTop.setting(interfaceInstanceAtTop_setting),
    .\interfaceInstanceAtTop.other_setting(interfaceInstanceAtTop_other_setting),
    .\interfaceInstanceAtTop.mysig_out(interfaceInstanceAtTop_mysig_out),
    .\interfaceInstanceAtTop.passThrough(interfaceInstanceAtTop_passThrough),
    .sig_out(sig_out)
  );

endmodule
