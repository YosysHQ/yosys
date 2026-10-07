module mcm_128_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1
);
  assign y0 = x * (-32'sd8190);
  assign y1 = x * (32'sd31457282);
endmodule
