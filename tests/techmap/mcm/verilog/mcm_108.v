module mcm_108_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2
);
  assign y0 = x * (-32'sd455066560);
  assign y1 = x * (-32'sd234880896);
  assign y2 = x * (-32'sd14708223);
endmodule
