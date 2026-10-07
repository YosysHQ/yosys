module mcm_115_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2
);
  assign y0 = x * (-32'sd4194295);
  assign y1 = x * (32'sd201326568);
  assign y2 = x * (32'sd2139111937);
endmodule
