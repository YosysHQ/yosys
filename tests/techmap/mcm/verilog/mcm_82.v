module mcm_82_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3,
  output wire signed [31:0] y4
);
  assign y0 = x * (32'sd156656);
  assign y1 = x * (32'sd34283520);
  assign y2 = x * (32'sd150995012);
  assign y3 = x * (32'sd1209008272);
  assign y4 = x * (32'sd1209270272);
endmodule
