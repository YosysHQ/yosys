module top;
	localparam BITS=8;

	struct packed {
		logic a;
		logic[BITS-1:0] b;
		byte c;
		logic x, y;
	} s;

	struct packed signed { 
		integer a;
		logic[15:0] b;
		logic[7:0] c;
		bit [7:0] d;
	} pack1;

	struct packed {
		byte a;
		struct packed {
			byte x, y;
		} b;
	} s2;

	assign s.a = '1;
	assign s.b = '1;
	assign s.c = 8'hAA;
	assign s.x = '1;
	logic[7:0] t;
	assign t = s.b;
	assign pack1.a = 42;
	assign pack1.b = 16'hAAAA;
	assign pack1.c = '1;
	assign pack1.d = 8'h55;
	assign s2.b.x = 'h42;

	always_comb assert(s.a == 1'b1);
	always_comb assert(s.c == 8'hAA);
	always_comb assert(s.x == 1'b1);
	always_comb assert(t == 8'hFF);
	always_comb assert(pack1.a == 42);
	always_comb assert(pack1.b == 16'hAAAA);
	always_comb assert(pack1.c == 8'hFF);
	always_comb assert(pack1[15:8] == 8'hFF);
	always_comb assert(pack1.d == 8'h55);
	always_comb assert(s2.b.x == 'h42);

endmodule
