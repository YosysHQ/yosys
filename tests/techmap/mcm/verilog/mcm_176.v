module mcm_176_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2
);
  assign y0 = x * (-32'sd48);
  assign y1 = x * (32'sd134217752);
  assign y2 = x * (32'sd1082114178);
endmodule
