module mcm_122_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3,
  output wire signed [31:0] y4
);
  assign y0 = x * (-32'sd3670016);
  assign y1 = x * (-32'sd3538922);
  assign y2 = x * (-32'sd32767);
  assign y3 = x * (-32'sd8);
  assign y4 = x * (32'sd268955640);
endmodule
