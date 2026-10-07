module mcm_63_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3
);
  assign y0 = x * (-32'sd142673536);
  assign y1 = x * (32'sd3334144);
  assign y2 = x * (32'sd8912864);
  assign y3 = x * (32'sd73530304);
endmodule
