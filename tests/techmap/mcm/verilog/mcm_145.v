module mcm_145_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3
);
  assign y0 = x * (-32'sd536846464);
  assign y1 = x * (-32'sd122876);
  assign y2 = x * (-32'sd47104);
  assign y3 = x * (32'sd805436420);
endmodule
