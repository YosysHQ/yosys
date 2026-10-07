module mcm_150_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3
);
  assign y0 = x * (-32'sd1048741714);
  assign y1 = x * (32'sd589968);
  assign y2 = x * (32'sd8521696);
  assign y3 = x * (32'sd532661172);
endmodule
