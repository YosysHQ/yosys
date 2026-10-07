module mcm_25_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3
);
  assign y0 = x * (-32'sd248524784);
  assign y1 = x * (-32'sd7831552);
  assign y2 = x * (32'sd1536);
  assign y3 = x * (32'sd7905);
endmodule
