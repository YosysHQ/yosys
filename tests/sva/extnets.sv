module top(input i, output o);
	A A();
	B B();
	assign A.i = i;
	assign o = B.o;
	always @* assert(o == i);
endmodule

module A;
	wire i, y;
`ifdef FAIL
	assign B.x = i;
`else
	assign B.x = !i;
`endif
	assign y = !B.y;
endmodule

module B;
	wire x, y, o;
	assign y = x, o = A.y;
endmodule
