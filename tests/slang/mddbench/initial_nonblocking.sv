module top(input clk, output reg q);
  initial q <= 1'b1;
  always @(posedge clk) q <= ~q;
endmodule
