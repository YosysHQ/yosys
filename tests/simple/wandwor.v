module wandwor_test0 (A, B, C, D, X, Y, Z);
	input A, B, C, D;
	output wor X;
	output wand Y;
	output Z;

	assign X = A, X = B, Y = C, Y = D;
	wandwor_foo foo_0 (C, D, X);
	wandwor_foo foo_1 (A, B, Y);
	wandwor_foo foo_2 (X, Y, Z);
endmodule

module wandwor_test1 (A, B, C, D, X, Y, Z);
	input [3:0] A, B, C, D;
	output wor [3:0] X;
	output wand [3:0] Y;
	output Z;

	wandwor_bar bar_inst (
		.I0({A, B}),
		.I1({B, A}),
		.O({X, Y})
	);

	assign X = C, X = D;
	assign Y = C, Y = D;
	assign Z = ^{X,Y};
endmodule

module wandwor_foo(input I0, I1, output O);
	assign O = I0 ^ I1;
endmodule

module wandwor_bar(input [7:0] I0, I1, output [7:0] O);
	assign O = I0 + I1;
endmodule
