module mcm_134_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3
);
  assign y0 = x * (-32'sd1078232063);
  assign y1 = x * (-32'sd287510460);
  assign y2 = x * (-32'sd34080766);
  assign y3 = x * (32'sd152145391);
endmodule
