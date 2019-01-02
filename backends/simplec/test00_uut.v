module test(input [31:0] a, b, c, output [31:0] x, y, z, w);
  unit_x unit_x_inst (.a(a), .b(b), .c(c), .x(x));
  unit_y unit_y_inst (.a(a), .b(b), .c(c), .y(y));
  assign z = a ^ b ^ c, w = z;
endmodule

module unit_x(input [31:0] a, b, c, output [31:0] x);
  assign x = (a & b) | c;
endmodule

module unit_y(input [31:0] a, b, c, output [31:0] y);
  assign y = a & (b | c);
endmodule

