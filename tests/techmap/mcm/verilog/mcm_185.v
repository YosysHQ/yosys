module mcm_185_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2
);
  assign y0 = x * (32'sd4128768);
  assign y1 = x * (32'sd74326896);
  assign y2 = x * (32'sd150994953);
endmodule
