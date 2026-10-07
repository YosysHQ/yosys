module mcm_56_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2
);
  assign y0 = x * (-32'sd536870752);
  assign y1 = x * (-32'sd28311548);
  assign y2 = x * (32'sd3136);
endmodule
