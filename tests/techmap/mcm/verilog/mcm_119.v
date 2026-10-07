module mcm_119_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3
);
  assign y0 = x * (-32'sd2094137333);
  assign y1 = x * (32'sd32894);
  assign y2 = x * (32'sd71303204);
  assign y3 = x * (32'sd536613120);
endmodule
