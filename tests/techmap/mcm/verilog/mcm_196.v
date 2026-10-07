module mcm_196_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3
);
  assign y0 = x * (32'sd147456);
  assign y1 = x * (32'sd296952);
  assign y2 = x * (32'sd742400);
  assign y3 = x * (32'sd503317440);
endmodule
