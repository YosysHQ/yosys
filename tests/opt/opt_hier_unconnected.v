module sub(input a, input b, output y, output z);
	assign y = a;
	assign z = a;
endmodule

module top(input x, output y);
	sub s(.a(x), .b(), .y(y), .z());
endmodule
