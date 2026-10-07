module mcm_172_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3
);
  assign y0 = x * (-32'sd33029680);
  assign y1 = x * (32'sd530612993);
  assign y2 = x * (32'sd569901328);
  assign y3 = x * (32'sd2113930304);
endmodule
