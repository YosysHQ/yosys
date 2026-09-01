module activity_window (input clk, input a, input b, input c, input d, output reg y);
  always @(posedge clk) y <= (a & b) | (c & d);
endmodule
