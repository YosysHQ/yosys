module mcm_186_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1,
  output wire signed [31:0] y2,
  output wire signed [31:0] y3,
  output wire signed [31:0] y4
);
  assign y0 = x * (-32'sd537134850);
  assign y1 = x * (-32'sd136314376);
  assign y2 = x * (-32'sd5240340);
  assign y3 = x * (32'sd33620095);
  assign y4 = x * (32'sd266209272);
endmodule
