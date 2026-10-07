module mcm_43_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2
);
  assign y0 = x * (32'sd600064);
  assign y1 = x * (32'sd17171712);
  assign y2 = x * (32'sd956301311);
endmodule
