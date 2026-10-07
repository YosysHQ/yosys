module mcm_141_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0
);
  assign y0 = x * (-32'sd32312);
endmodule
