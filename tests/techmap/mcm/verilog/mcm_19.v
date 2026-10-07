module mcm_19_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2
);
  assign y0 = x * (-32'sd67139583);
  assign y1 = x * (-32'sd33832320);
  assign y2 = x * (32'sd336759288);
endmodule
