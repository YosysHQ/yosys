module mcm_170_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2
);
  assign y0 = x * (32'sd65537);
  assign y1 = x * (32'sd268439297);
  assign y2 = x * (32'sd538189840);
endmodule
