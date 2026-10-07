module mcm_168_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3,
  output wire signed [31:0] y4,
  output wire signed [31:0] y5
);
  assign y0 = x * (-32'sd264242160);
  assign y1 = x * (-32'sd4194318);
  assign y2 = x * (-32'sd64);
  assign y3 = x * (32'sd6291480);
  assign y4 = x * (32'sd33554563);
  assign y5 = x * (32'sd1090523201);
endmodule
