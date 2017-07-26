module top (input clk, input [7:0] a, b, output reg [15:0] c);
  always @(posedge clk) c <= a * b;
endmodule
