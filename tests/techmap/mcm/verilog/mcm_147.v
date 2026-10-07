module mcm_147_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3
);
  assign y0 = x * (-32'sd68697216);
  assign y1 = x * (32'sd608310279);
  assign y2 = x * (32'sd1081321246);
  assign y3 = x * (32'sd1344340992);
endmodule
