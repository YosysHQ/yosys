module mcm_5_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3
);
  assign y0 = x * (-32'sd1082128367);
  assign y1 = x * (-32'sd541063926);
  assign y2 = x * (-32'sd16906224);
  assign y3 = x * (32'sd541065732);
endmodule
