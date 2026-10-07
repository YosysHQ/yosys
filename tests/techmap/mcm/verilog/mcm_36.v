module mcm_36_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3,
  output wire signed [31:0] y4
);
  assign y0 = x * (-32'sd133039168);
  assign y1 = x * (32'sd1571456);
  assign y2 = x * (32'sd268214265);
  assign y3 = x * (32'sd537459840);
  assign y4 = x * (32'sd1039044732);
endmodule
