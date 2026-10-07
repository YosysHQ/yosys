module mcm_131_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1
);
  assign y0 = x * (-32'sd1745354705);
  assign y1 = x * (32'sd335806463);
endmodule
