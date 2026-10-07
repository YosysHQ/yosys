module mcm_52_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2
);
  assign y0 = x * (-32'sd169050112);
  assign y1 = x * (-32'sd33552368);
  assign y2 = x * (32'sd16973824);
endmodule
