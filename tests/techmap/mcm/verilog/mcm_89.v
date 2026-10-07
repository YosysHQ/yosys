module mcm_89_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2
);
  assign y0 = x * (-32'sd2080374722);
  assign y1 = x * (32'sd2097153);
  assign y2 = x * (32'sd1887433208);
endmodule
