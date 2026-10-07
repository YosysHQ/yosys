module mcm_65_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3
);
  assign y0 = x * (-32'sd533794690);
  assign y1 = x * (32'sd133695480);
  assign y2 = x * (32'sd1069532218);
  assign y3 = x * (32'sd1069678096);
endmodule
