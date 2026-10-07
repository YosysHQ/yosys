module mcm_107_unoptimized(
  input wire signed [31:0] x,
  output wire signed [31:0] y0,
  output wire signed [31:0] y1
);
  assign y0 = x * (-32'sd545431471);
  assign y1 = x * (32'sd707854336);
endmodule
