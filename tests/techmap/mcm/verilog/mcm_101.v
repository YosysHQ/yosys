module mcm_101_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0
);
  assign y0 = x * (32'sd4194304);
endmodule
