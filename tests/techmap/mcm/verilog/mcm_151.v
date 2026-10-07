module mcm_151_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2
);
  assign y0 = x * (-32'sd1610611708);
  assign y1 = x * (-32'sd377487359);
  assign y2 = x * (32'sd1207959549);
endmodule
