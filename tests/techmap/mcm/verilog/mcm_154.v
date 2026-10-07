module mcm_154_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2
);
  assign y0 = x * (-32'sd2097120);
  assign y1 = x * (-32'sd9144);
  assign y2 = x * (32'sd5120);
endmodule
