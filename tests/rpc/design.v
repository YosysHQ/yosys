module top(input [3:0] i, output [3:0] o);
	python_inv #(
	  .width(4)
	) inv (
		.i(i),
		.o(o),
	);
endmodule
