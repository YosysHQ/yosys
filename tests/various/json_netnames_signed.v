module top(input signed [15:0] a, output [31:0] y);
  wire signed [15:0] t;
  assign t = a;
  assign y = t;
endmodule
