module wreduce_test0(input [7:0] a, b, output [15:0] x, y, z);
  assign x = -$signed({1'b0, a});
  assign y = $signed({1'b0, a}) + $signed({1'b0, b});
  assign z = x ^ y;
endmodule

module wreduce_test1(input [31:0] a, b, output [7:0] x, y, z, w);
  assign x = a - b, y = a * b, z = a >> b, w = a << b;
endmodule
