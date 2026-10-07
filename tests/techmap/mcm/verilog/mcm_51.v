module mcm_51_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3
);
  assign y0 = x * (-32'sd20447088);
  assign y1 = x * (-32'sd7143374);
  assign y2 = x * (32'sd13008800);
  assign y3 = x * (32'sd129879041);
endmodule
