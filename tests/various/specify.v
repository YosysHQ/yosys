module test (
	input EN, CLK,
	input [3:0] D,
	output reg [3:0] Q
);
	always @(posedge CLK)
		if (EN) Q <= D;

	specify
		if (EN) (CLK *> (Q : D)) = (1, 2:3:4);
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
