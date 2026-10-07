module mcm_106_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3,
  output wire signed [31:0] y4
);
  assign y0 = x * (-32'sd142606082);
  assign y1 = x * (-32'sd4604911);
  assign y2 = x * (32'sd8132);
  assign y3 = x * (32'sd2080832);
  assign y4 = x * (32'sd142605758);
endmodule
