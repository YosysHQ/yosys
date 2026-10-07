module mcm_180_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3,
  output wire signed [31:0] y4
);
  assign y0 = x * (-32'sd2113708024);
  assign y1 = x * (-32'sd1056853981);
  assign y2 = x * (-32'sd4716416);
  assign y3 = x * (32'sd257989);
  assign y4 = x * (32'sd933916);
endmodule
