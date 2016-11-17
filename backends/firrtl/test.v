module test(input clk, signed input [7:0] a, b, x, output [15:0] s, d, y, z, u, q);
  assign s = a+{b[6:2], 2'b1}, d = a-b, y = x, z[7:0] = s+d, z[15:8] = s-d;
  always @(posedge clk) q <= s ^ d ^ x;
endmodule
