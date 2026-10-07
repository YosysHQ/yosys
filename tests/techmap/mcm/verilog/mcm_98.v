module mcm_98_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3
);
  assign y0 = x * (-32'sd266238);
  assign y1 = x * (32'sd2068);
  assign y2 = x * (32'sd17416);
  assign y3 = x * (32'sd261888);
endmodule
