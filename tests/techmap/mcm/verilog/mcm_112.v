module mcm_112_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1
);
  assign y0 = x * (32'sd6192);
  assign y1 = x * (32'sd1610609662);
endmodule
