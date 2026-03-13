module sub_3op(
	input  [7:0] a, b, c,
	output [7:0] y
);
	assign y = a - b + c;
endmodule
