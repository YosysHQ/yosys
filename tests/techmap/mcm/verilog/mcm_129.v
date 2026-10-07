module mcm_129_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3
);
  assign y0 = x * (-32'sd570425310);
  assign y1 = x * (-32'sd8912894);
  assign y2 = x * (-32'sd4194303);
  assign y3 = x * (32'sd1140989918);
endmodule
