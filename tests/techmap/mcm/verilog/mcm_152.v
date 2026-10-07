module mcm_152_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2
);
  assign y0 = x * (-32'sd252698624);
  assign y1 = x * (32'sd33816060);
  assign y2 = x * (32'sd1071609924);
endmodule
