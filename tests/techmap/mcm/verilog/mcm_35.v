module mcm_35_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2
);
  assign y0 = x * (32'sd31592222);
  assign y1 = x * (32'sd518062088);
  assign y2 = x * (32'sd2021776945);
endmodule
