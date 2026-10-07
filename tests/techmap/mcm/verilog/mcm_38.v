module mcm_38_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3,
  output wire signed [31:0] y4
);
  assign y0 = x * (32'sd33554239);
  assign y1 = x * (32'sd268451857);
  assign y2 = x * (32'sd318786561);
  assign y3 = x * (32'sd1074257920);
  assign y4 = x * (32'sd1074856004);
endmodule
