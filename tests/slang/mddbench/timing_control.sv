module top(input clk, d, output reg q);
  always @(posedge clk) q <= #1 d;
endmodule
