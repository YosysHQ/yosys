module mcm_68_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3
);
  assign y0 = x * (-32'sd268533758);
  assign y1 = x * (-32'sd33357812);
  assign y2 = x * (32'sd142755868);
  assign y3 = x * (32'sd178280955);
endmodule
