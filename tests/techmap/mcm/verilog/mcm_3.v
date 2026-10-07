module mcm_3_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3
);
  assign y0 = x * (-32'sd542109663);
  assign y1 = x * (-32'sd533643263);
  assign y2 = x * (32'sd410058752);
  assign y3 = x * (32'sd1088462846);
endmodule
