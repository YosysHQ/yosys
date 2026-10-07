module mcm_96_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3
);
  assign y0 = x * (-32'sd805310376);
  assign y1 = x * (-32'sd780140451);
  assign y2 = x * (32'sd536869696);
  assign y3 = x * (32'sd805308328);
endmodule
