module mcm_182_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3
);
  assign y0 = x * (32'sd1671296);
  assign y1 = x * (32'sd4168532);
  assign y2 = x * (32'sd213909632);
  assign y3 = x * (32'sd1140850653);
endmodule
