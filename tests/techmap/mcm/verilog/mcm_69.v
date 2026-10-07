module mcm_69_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3
);
  assign y0 = x * (-32'sd1140851232);
  assign y1 = x * (-32'sd17825791);
  assign y2 = x * (32'sd1152);
  assign y3 = x * (32'sd602865664);
endmodule
