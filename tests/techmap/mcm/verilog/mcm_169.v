module mcm_169_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3
);
  assign y0 = x * (-32'sd16380);
  assign y1 = x * (32'sd8388352);
  assign y2 = x * (32'sd12582912);
  assign y3 = x * (32'sd16777214);
endmodule
