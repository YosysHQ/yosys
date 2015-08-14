
// test cases found using vloghammer
// https://github.com/cliffordwolf/VlogHammer

module test01(a, y);
  input [7:0] a;
  output [3:0] y;
  assign y = ~a >> 4;
endmodule

module test02(a, y);
  input signed [3:0] a;
  output signed [4:0] y;
  assign y = (~a) >> 1;
endmodule

module test03(a, b, y);
  input [2:0] a;
  input signed [1:0] b;
  output y;
  assign y = ~(a >>> 1) == b;
endmodule

module test04(a, y);
  input a;
  output [1:0] y;
  assign y = ~(a - 1'b0);
endmodule

// .. this test triggers a bug in Xilinx ISIM.
// module test05(a, y);
//   input a;
//   output y;
//   assign y = 12345 >> {a, 32'd0};
// endmodule

// .. this test triggers a bug in Icarus Verilog.
// module test06(a, b, c, y);
//   input signed [3:0] a;
//   input signed [1:0] b;
//   input signed [1:0] c;
//   output [5:0] y;
//   assign y = (a >> b) >>> c;
// endmodule

module test07(a, b, y);
  input signed [1:0] a;
  input signed [2:0] b;
  output y;
  assign y = 2'b11 != a+b;
endmodule

module test08(a, b, y);
  input [1:0] a;
  input [1:0] b;
  output y;
  assign y = a == ($signed(b) >>> 1);
endmodule

module test09(a, b, c, y);
  input a;
  input signed [1:0] b;
  input signed [2:0] c;
  output [3:0] y;
  assign y = a ? b : c;
endmodule

module test10(a, b, c, y);
  input a;
  input signed [1:0] b;
  input signed [2:0] c;
  output y;
  assign y = ^(a ? b : c);
endmodule

// module test11(a, b, y);
//   input signed [3:0] a;
//   input signed [3:0] b;
//   output signed [5:0] y;
//   assign y = -(5'd27);
// endmodule

