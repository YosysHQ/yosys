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
		s.a[-1] = '0;

		s.b = '1;
		s.b[1:0] = '0;
	end

	always_comb assert(s==64'h4200_0012_3400_FFFC);
	always_comb assert(s.a[0][3:-4]===8'h0x);
	always_comb assert(s.b[23:16]===8'hxx);
	always_comb assert(s.b[19:12]===8'hxf);

	// Same as s, but defining dimensions in stages with typedef
	typedef bit [7:0] bit8_t;
	struct packed {
		bit8_t [5:0] a;		// 6 element packed array of bytes
		bit [15:0] b;		// filler for non-zero offset
	} s_s;

	initial begin
		s_s = '0;

		s_s.a[2:1] = 16'h1234;
		s_s.a[5] = 8'h42;
		s_s.a[-1] = '0;

		s_s.b = '1;
		s_s.b[1:0] = '0;
	end

	always_comb assert(s_s==64'h4200_0012_3400_FFFC);
	always_comb assert(s_s.a[0][3:-4]===8'h0x);
	always_comb assert(s_s.b[23:16]===8'hxx);
	always_comb assert(s_s.b[19:12]===8'hxf);

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

	// Same as s2, but with little endian addressing
	struct packed {
		bit [0:7] [7:0] a;	// 8 element packed array of bytes
		bit [0:15] b;		// filler for non-zero offset
	} s3;

	initial begin
		s3 = '0;

		s3.a[5:6] = 16'h1234;
		s3.a[2] = 8'h42;

		s3.a[0] = '1;
		s3.a[0][1:0] = '0;

		s3.b = '1;
		s3.b[14:15] = '0;
	end

	always_comb assert(s3==80'hFC00_4200_0012_3400_FFFC);

	// Same as s3, but with little endian bit addressing
	struct packed {
		bit [0:7] [0:7] a;	// 8 element packed array of bytes
		bit [0:15] b;		// filler for non-zero offset
	} s3_b;

	initial begin
		s3_b = '0;

		s3_b.a[5:6] = 16'h1234;
		s3_b.a[2] = 8'h42;

		s3_b.a[0] = '1;
		s3_b.a[0][6:7] = '0;

		s3_b.b = '1;
		s3_b.b[14:15] = '0;
	end

	always_comb assert(s3_b==80'hFC00_4200_0012_3400_FFFC);

	struct packed {
		bit [0:7] [0:1] [0:3] a;
		bit [0:15] b;		// filler for non-zero offset
	} s3_lll;

	initial begin
		s3_lll = '0;

		s3_lll.a[5:6] = 16'h1234;
		s3_lll.a[2] = 8'h42;

		s3_lll.a[0] = '1;
		s3_lll.a[0][1][2:3] = '0;

		s3_lll.b = '1;
		s3_lll.b[14:15] = '0;
	end

	always_comb assert(s3_lll==80'hFC00_4200_0012_3400_FFFC);

	struct packed {
		bit [0:7] [1:0] [0:3] a;
		bit [0:15] b;		// filler for non-zero offset
	} s3_lbl;

	initial begin
		s3_lbl = '0;

		s3_lbl.a[5:6] = 16'h1234;
		s3_lbl.a[2] = 8'h42;

		s3_lbl.a[0] = '1;
		s3_lbl.a[0][0][2:3] = '0;

		s3_lbl.b = '1;
		s3_lbl.b[14:15] = '0;
	end

	always_comb assert(s3_lbl==80'hFC00_4200_0012_3400_FFFC);

	// Same as s3_lbl, but defining dimensions in stages with typedef
	typedef bit [0:3] bit3l_t;
	struct packed {
		bit3l_t [0:7] [1:0] a;
		bit [0:15] b;		// filler for non-zero offset
	} s3_lbl_s;

	initial begin
		s3_lbl_s = '0;

		s3_lbl_s.a[5:6] = 16'h1234;
		s3_lbl_s.a[2] = 8'h42;

		s3_lbl_s.a[0] = '1;
		s3_lbl_s.a[0][0][2:3] = '0;

		s3_lbl_s.b = '1;
		s3_lbl_s.b[14:15] = '0;
	end

	always_comb assert(s3_lbl_s==80'hFC00_4200_0012_3400_FFFC);

	struct packed {
		bit [0:7] [0:1] [3:0] a;
		bit [0:15] b;		// filler for non-zero offset
	} s3_llb;

	initial begin
		s3_llb = '0;

		s3_llb.a[5:6] = 16'h1234;
		s3_llb.a[2] = 8'h42;

		s3_llb.a[0] = '1;
		s3_llb.a[0][1][1:0] = '0;

		s3_llb.b = '1;
		s3_llb.b[14:15] = '0;
	end

	always_comb assert(s3_llb==80'hFC00_4200_0012_3400_FFFC);

	struct packed {
		bit [-10:-3] [-2:-1] [5:2] a;
		bit [0:15] b;		// filler for non-zero offset
	} s3_off;

	initial begin
		s3_off = '0;

		s3_off.a[-5:-4] = 16'h1234;
		s3_off.a[-8] = 8'h42;

		s3_off.a[-10] = '1;
		s3_off.a[-10][-1][3:0] = '0;

		s3_off.b = '1;
		s3_off.b[14:15] = '0;
	end

	always_comb assert(s3_off==80'hFC00_4200_0012_3400_FFFC);

`ifndef VERIFIC
	// Note that the tests below for unpacked arrays in structs rely on the
	// fact that they are actually packed in Yosys.

	// Same as s2, but using unpacked array syntax
	struct packed {
		bit [7:0] a [7:0];	// 8 element unpacked array of bytes
		bit [15:0] b;		// filler for non-zero offset
	} s4;

	initial begin
		s4 = '0;

		s4.a[2:1] = 16'h1234;
		s4.a[5] = 8'h42;

		s4.a[7] = '1;
		s4.a[7][1:0] = '0;

		s4.b = '1;
		s4.b[1:0] = '0;
	end

	always_comb assert(s4==80'hFC00_4200_0012_3400_FFFC);

	// Same as s3, but using unpacked array syntax
	struct packed {
		bit [7:0] a [0:7];	// 8 element unpacked array of bytes
		bit [0:15] b;		// filler for non-zero offset
	} s5;

	initial begin
		s5 = '0;

		s5.a[5:6] = 16'h1234;
		s5.a[2] = 8'h42;

		s5.a[0] = '1;
		s5.a[0][1:0] = '0;

		s5.b = '1;
		s5.b[14:15] = '0;
	end

	always_comb assert(s5==80'hFC00_4200_0012_3400_FFFC);

	// Same as s5, but with little endian bit addressing
	struct packed {
		bit [0:7] a [0:7];	// 8 element unpacked array of bytes
		bit [0:15] b;		// filler for non-zero offset
	} s5_b;

	initial begin
		s5_b = '0;

		s5_b.a[5:6] = 16'h1234;
		s5_b.a[2] = 8'h42;

		s5_b.a[0] = '1;
		s5_b.a[0][6:7] = '0;

		s5_b.b = '1;
		s5_b.b[14:15] = '0;
	end

	always_comb assert(s5_b==80'hFC00_4200_0012_3400_FFFC);

	// Same as s5, but using C-type unpacked array syntax
	struct packed {
		bit [7:0] a [8];	// 8 element unpacked array of bytes
		bit [0:15] b;		// filler for non-zero offset
	} s6;

	initial begin
		s6 = '0;

		s6.a[5:6] = 16'h1234;
		s6.a[2] = 8'h42;

		s6.a[0] = '1;
		s6.a[0][1:0] = '0;

		s6.b = '1;
		s6.b[14:15] = '0;
	end

	always_comb assert(s6==80'hFC00_4200_0012_3400_FFFC);
`endif

endmodule
