// test for array indexing in structures

module top;
	
	struct packed {
		bit [5:0] [7:0] a;	// 6 element packed array of bytes
		bit [15:0] b;		// filler for non-zero offset
	} s;

	initial begin
		s = '0;

		s.a[2:1] = 16'h1234;
		s.a[5] = 8'h42;

		s.b = '1;
		s.b[1:0] = '0;
	end

	always_comb assert(s==64'h4200_0012_3400_FFFC);

endmodule
