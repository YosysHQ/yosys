module mcm_97_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3
);
  assign y0 = x * (-32'sd1105197029);
  assign y1 = x * (32'sd44040184);
  assign y2 = x * (32'sd71991294);
  assign y3 = x * (32'sd570424048);
endmodule
