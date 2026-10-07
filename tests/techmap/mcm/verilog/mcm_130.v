module mcm_130_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2
);
  assign y0 = x * (32'sd4161036);
  assign y1 = x * (32'sd71826952);
  assign y2 = x * (32'sd270532606);
endmodule
