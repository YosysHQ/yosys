module foo #(parameter [1:0] a) (output [1:0] o);
	assign o = a;
endmodule

module top(output [1:0] o);
	foo #(2'b0x) foo(o);
	always_comb begin
		assert(o == 2'b00);
	end
endmodule
