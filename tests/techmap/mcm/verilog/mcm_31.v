module mcm_31_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3
);
  assign y0 = x * (32'sd68681728);
  assign y1 = x * (32'sd1648754696);
  assign y2 = x * (32'sd1657274497);
  assign y3 = x * (32'sd1893728256);
endmodule
