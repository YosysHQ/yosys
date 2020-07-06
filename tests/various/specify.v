module test (
	input EN, CLK,
	input [3:0] D,
	output reg [3:0] Q
);
	always @(posedge CLK)
		if (EN) Q <= D;

	specify
`ifndef SKIP_UNSUPPORTED_IGN_PARSER_CONSTRUCTS
		if (EN) (posedge CLK *> (Q : D)) = (1, 2:3:4);
		$setup(D, posedge CLK &&& EN, 5);
		$hold(posedge CLK, D &&& EN, 6);
`endif
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
