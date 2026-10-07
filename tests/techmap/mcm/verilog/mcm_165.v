module mcm_165_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3,
  output wire signed [31:0] y4
);
  assign y0 = x * (-32'sd4128248);
  assign y1 = x * (32'sd48);
  assign y2 = x * (32'sd33558529);
  assign y3 = x * (32'sd134234100);
  assign y4 = x * (32'sd251693048);
endmodule
