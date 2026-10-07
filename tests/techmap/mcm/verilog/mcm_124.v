module mcm_124_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3
);
  assign y0 = x * (-32'sd1081884667);
  assign y1 = x * (-32'sd135249920);
  assign y2 = x * (-32'sd134217632);
  assign y3 = x * (-32'sd8388600);
endmodule
