module mcm_179_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3,
  output wire signed [31:0] y4
);
  assign y0 = x * (-32'sd67096568);
  assign y1 = x * (32'sd294904);
  assign y2 = x * (32'sd4194305);
  assign y3 = x * (32'sd16781312);
  assign y4 = x * (32'sd33554464);
endmodule
