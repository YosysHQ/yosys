module mcm_45_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3,
  output wire signed [31:0] y4
);
  assign y0 = x * (-32'sd469729220);
  assign y1 = x * (32'sd4163566);
  assign y2 = x * (32'sd8421376);
  assign y3 = x * (32'sd134218241);
  assign y4 = x * (32'sd201359361);
endmodule
