module mcm_90_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0
);
  assign y0 = x * (32'sd1800);
endmodule
