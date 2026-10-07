module mcm_17_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3,
  output wire signed [31:0] y4
);
  assign y0 = x * (-32'sd1082134496);
  assign y1 = x * (-32'sd228197255);
  assign y2 = x * (-32'sd118424004);
  assign y3 = x * (32'sd3670030);
  assign y4 = x * (32'sd1081872417);
endmodule
