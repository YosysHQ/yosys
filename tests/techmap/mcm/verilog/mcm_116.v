module mcm_116_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3
);
  assign y0 = x * (-32'sd3162497);
  assign y1 = x * (-32'sd2097148);
  assign y2 = x * (32'sd1048580);
  assign y3 = x * (32'sd136839677);
endmodule
