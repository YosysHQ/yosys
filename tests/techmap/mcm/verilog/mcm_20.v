module mcm_20_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3,
  output wire signed [31:0] y4
);
  assign y0 = x * (-32'sd1073741804);
  assign y1 = x * (-32'sd1073675260);
  assign y2 = x * (-32'sd268441695);
  assign y3 = x * (-32'sd268335615);
  assign y4 = x * (32'sd67108863);
endmodule
