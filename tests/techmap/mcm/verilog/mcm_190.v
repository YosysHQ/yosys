module mcm_190_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3
);
  assign y0 = x * (-32'sd2130182145);
  assign y1 = x * (-32'sd1073719305);
  assign y2 = x * (-32'sd1073707016);
  assign y3 = x * (-32'sd324624);
endmodule
