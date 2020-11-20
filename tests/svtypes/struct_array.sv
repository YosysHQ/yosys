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

	struct packed {
		bit [7:0] [7:0] a;	// 8 element packed array of bytes
		bit [15:0] b;		// filler for non-zero offset
	} s2;

	initial begin
		s2 = '0;

		s2.a[2:1] = 16'h1234;
		s2.a[5] = 8'h42;

		s2.a[7] = '1;
		s2.a[7][1:0] = '0;

		s2.b = '1;
		s2.b[1:0] = '0;
	end

	always_comb assert(s2==80'hFC00_4200_0012_3400_FFFC);

endmodule
