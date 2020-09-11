package p;

typedef struct packed {
	byte a;
	byte b;
} p_t;

endpackage


module top;

	typedef logic[7:0] t_t;

	typedef struct packed {
		bit		a;
		logic[7:0]	b;
		t_t		t;
	} s_t;

	s_t s;
	s_t s1;

	p::p_t ps;

	assign s.a = '1;
	assign s.b = '1;
	assign s.t = 8'h55;
	assign s1 = s;
	assign ps.a = 8'hAA;
	assign ps.b = 8'h55;

	always_comb begin
		assert(s.a == 1'b1);
		assert(s.b == 8'hFF);
		assert(s.t == 8'h55);
		assert(s1.t == 8'h55);
		assert(ps.a == 8'hAA);
		assert(ps.b == 8'h55);
	end

endmodule
