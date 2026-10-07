module mcm_164_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3
);
  assign y0 = x * (-32'sd533732819);
  assign y1 = x * (-32'sd520176);
  assign y2 = x * (32'sd1568784);
  assign y3 = x * (32'sd192613178);
endmodule
