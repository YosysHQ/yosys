module mcm_191_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2
);
  assign y0 = x * (-32'sd2145517567);
  assign y1 = x * (32'sd3140608);
  assign y2 = x * (32'sd2145516545);
endmodule
