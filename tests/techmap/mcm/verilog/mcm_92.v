module mcm_92_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3,
  output wire signed [31:0] y4
);
  assign y0 = x * (-32'sd2013265888);
  assign y1 = x * (-32'sd943841250);
  assign y2 = x * (-32'sd738328552);
  assign y3 = x * (32'sd538968052);
  assign y4 = x * (32'sd1006649312);
endmodule
