module mcm_126_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2
);
  assign y0 = x * (32'sd8982528);
  assign y1 = x * (32'sd268433406);
  assign y2 = x * (32'sd2147483631);
endmodule
