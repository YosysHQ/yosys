module mcm_149_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3
);
  assign y0 = x * (32'sd33587232);
  assign y1 = x * (32'sd134151169);
  assign y2 = x * (32'sd536604676);
  assign y3 = x * (32'sd1611396097);
endmodule
