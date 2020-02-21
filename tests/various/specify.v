module test (
	input EN, CLK,
	input [3:0] D,
	output reg [3:0] Q
);
	always @(posedge CLK)
		if (EN) Q <= D;

	specify
		if (EN) (posedge CLK *> (Q : D)) = (1, 2:3:4);
		$setup(D, posedge CLK &&& EN, 5);
		$hold(posedge CLK, D &&& EN, 6);
	endspecify
endmodule

module test2 (
	input A, B,
	output Q
);
	xor (Q, A, B);
	specify
		//specparam T_rise = 1;
		//specparam T_fall = 2;
		`define T_rise 1
		`define T_fall 2
		(A => Q) = (`T_rise,`T_fall);
		//(B => Q) = (`T_rise+`T_fall)/2.0;
		(B => Q) = 1.5;
	endspecify
endmodule

module issue01144(input clk, d, output q);
specify
  (posedge clk => (q +: d)) = (3,1);
  (posedge clk *> (q +: d)) = (3,1);
endspecify
endmodule

module test3(input clk, input [1:0] d, output [1:0] q);
specify
  (posedge clk => (q +: d)) = (3,1);
  (posedge clk *> (q +: d)) = (3,1);
endspecify
endmodule

module test4(input clk, d, output q);
specify
  $setup(d, posedge clk, 1:2:3);
  $setuphold(d, posedge clk, 1:2:3, 4:5:6);
endspecify
endmodule

module test5(input clk, d, e, output q);
specify
  $setup(d, posedge clk &&& e, 1:2:3);
endspecify
endmodule

module test6(input clk, d, e, output q);
specify
  (d[0] *> q[0]) = (3,1);
  (posedge clk[0] => (q[0] +: d[0])) = (3,1);
endspecify
endmodule
