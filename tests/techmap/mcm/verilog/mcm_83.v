module mcm_83_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3,
  output wire signed [31:0] y4
);
  assign y0 = x * (32'sd8386556);
  assign y1 = x * (32'sd134283199);
  assign y2 = x * (32'sd807403105);
  assign y3 = x * (32'sd1073740312);
  assign y4 = x * (32'sd1614806276);
endmodule
