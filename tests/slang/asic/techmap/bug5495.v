module simple(I1, I2, O);
	input wire I1;
	input wire I2;
	output wire O;

	assign O = I1 | I2;
endmodule
