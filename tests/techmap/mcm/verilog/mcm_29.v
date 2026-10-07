module mcm_29_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2
);
  assign y0 = x * (-32'sd117454844);
  assign y1 = x * (-32'sd10751);
  assign y2 = x * (32'sd520192);
endmodule
