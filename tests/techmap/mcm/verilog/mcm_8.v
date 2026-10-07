module mcm_8_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3
);
  assign y0 = x * (-32'sd1077735408);
  assign y1 = x * (-32'sd16842748);
  assign y2 = x * (32'sd1052736);
  assign y3 = x * (32'sd16839168);
endmodule
