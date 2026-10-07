module mcm_58_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1
);
  assign y0 = x * (32'sd8388848);
  assign y1 = x * (32'sd538967036);
endmodule
