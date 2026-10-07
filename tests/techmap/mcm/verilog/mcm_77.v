module mcm_77_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2
);
  assign y0 = x * (-32'sd503320316);
  assign y1 = x * (-32'sd455081488);
  assign y2 = x * (-32'sd115867540);
endmodule
