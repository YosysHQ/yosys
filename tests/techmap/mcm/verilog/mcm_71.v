module mcm_71_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3
);
  assign y0 = x * (-32'sd19927040);
  assign y1 = x * (32'sd126115872);
  assign y2 = x * (32'sd270432414);
  assign y3 = x * (32'sd1342439423);
endmodule
