module mcm_50_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2
);
  assign y0 = x * (-32'sd65189894);
  assign y1 = x * (32'sd134483904);
  assign y2 = x * (32'sd386727944);
endmodule
