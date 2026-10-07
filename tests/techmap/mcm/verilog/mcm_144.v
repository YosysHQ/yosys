module mcm_144_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2
);
  assign y0 = x * (-32'sd33570144);
  assign y1 = x * (32'sd116391950);
  assign y2 = x * (32'sd1893713920);
endmodule
