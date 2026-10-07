module mcm_120_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1
);
  assign y0 = x * (-32'sd536862722);
  assign y1 = x * (32'sd402651137);
endmodule
