module mcm_53_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2
);
  assign y0 = x * (32'sd33621058);
  assign y1 = x * (32'sd67110912);
  assign y2 = x * (32'sd1612775424);
endmodule
