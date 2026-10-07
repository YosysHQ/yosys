module mcm_76_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2
);
  assign y0 = x * (-32'sd1072692225);
  assign y1 = x * (-32'sd255);
  assign y2 = x * (32'sd294912);
endmodule
