// These tests are adapted from tests/sat/sizebits.sv

module top;

typedef struct packed {
	logic [2:7][3:0] y;
} sy_t;

struct packed {
	logic t;
	logic [5:2] x;
	sy_t sy;
	union packed {
		logic [7:2][2:9][1:4] z;
		logic [1:6*8*4] z2;
	} sz;
} s;

//wire [$size(s.x)-1:0]x_size;
//wire [$size({s.x, s.x})-1:0]xx_size;
//wire [$size(s.sy.y)-1:0]y_size;
//wire [$size(s.sz.z)-1:0]z_size;

//wire [$bits(s.x)-1:0]x_bits;
//wire [$bits({s.x, s.x})-1:0]xx_bits;

always_comb begin
	assert ($dimensions(s) == 1);
	assert ($dimensions(s.x) == 1);
`ifndef VERIFIC
	assert ($dimensions(s.t) == 1);
	assert ($dimensions({3{s.x}}) == 1);
`endif
	assert ($dimensions(s.sy.y) == 2);
	assert ($dimensions(s.sy.y[2]) == 1);
	assert ($dimensions(s.sz.z) == 3);
	assert ($dimensions(s.sz.z[3]) == 2);
	assert ($dimensions(s.sz.z[3][3]) == 1);

	assert ($size(s) == $size(s.t) + $size(s.x) + $size(s.sy) + $size(s.sz));
	assert ($size(s) == 1 + 4 + 6*4 + 6*8*4);

	assert ($size(s.t) == 1);
	assert ($size(s.x) == 4);
`ifndef VERIFIC
	assert ($size({3{s.x}}) == 3*4);
`endif
	assert ($size(s.sy.y) == 6);
	assert ($size(s.sy.y, 1) == 6);
	assert ($size(s.sy.y, (1+1)) == 4);
	assert ($size(s.sy.y[2], 1) == 4);
	// This is unsupported at the moment
	//	assert ($size(s.sy.y[2][1], 1) == 1);

	assert ($size(s.sz.z) == 6);
	assert ($size(s.sz.z, 1) == 6);
	assert ($size(s.sz.z, 2) == 8);
	assert ($size(s.sz.z, 3) == 4);
	assert ($size(s.sz.z[3], 1) == 8);
	assert ($size(s.sz.z[3][3], 1) == 4);
	// This is unsupported at the moment
	//	assert ($size(s.sz.z[3][3][3], 1) == 1);
	// This should trigger an error if enabled (it does).
	//	assert ($size(s.sz.z, 4) == 4);

	assert ($bits(s.t) == 1);
	assert ($bits(s.x) == 4);
	assert ($bits(s.sy.y) == 4*6);
	assert ($bits(s.sz.z) == 4*6*8);

	assert ($high(s.x) == 5);
	assert ($high(s.sy.y) == 7);
	assert ($high(s.sy.y, 1) == 7);
	assert ($high(s.sy.y, (1+1)) == 3);

	assert ($high(s.sz.z) == 7);
	assert ($high(s.sz.z, 1) == 7);
	assert ($high(s.sz.z, 2) == 9);
	assert ($high(s.sz.z, 3) == 4);
	assert ($high(s.sz.z[3]) == 9);
	assert ($high(s.sz.z[3][3]) == 4);
	assert ($high(s.sz.z[3], 2) == 4);

	assert ($low(s.x) == 2);
	assert ($low(s.sy.y) == 2);
	assert ($low(s.sy.y, 1) == 2);
	assert ($low(s.sy.y, (1+1)) == 0);

	assert ($low(s.sz.z) == 2);
	assert ($low(s.sz.z, 1) == 2);
	assert ($low(s.sz.z, 2) == 2);
	assert ($low(s.sz.z, 3) == 1);
	assert ($low(s.sz.z[3]) == 2);
	assert ($low(s.sz.z[3][3]) == 1);
	assert ($low(s.sz.z[3], 2) == 1);

	assert ($left(s.x) == 5);
	assert ($left(s.sy.y) == 2);
	assert ($left(s.sy.y, 1) == 2);
	assert ($left(s.sy.y, (1+1)) == 3);

	assert ($left(s.sz.z) == 7);
	assert ($left(s.sz.z, 1) == 7);
	assert ($left(s.sz.z, 2) == 2);
	assert ($left(s.sz.z, 3) == 1);
	assert ($left(s.sz.z[3]) == 2);
	assert ($left(s.sz.z[3][3]) == 1);
	assert ($left(s.sz.z[3], 2) == 1);

	assert ($right(s.x) == 2);
	assert ($right(s.sy.y) == 7);
	assert ($right(s.sy.y, 1) == 7);
	assert ($right(s.sy.y, (1+1)) == 0);

	assert ($right(s.sz.z) == 2);
	assert ($right(s.sz.z, 1) == 2);
	assert ($right(s.sz.z, 2) == 9);
	assert ($right(s.sz.z, 3) == 4);
	assert ($right(s.sz.z[3]) == 9);
	assert ($right(s.sz.z[3][3]) == 4);
	assert ($right(s.sz.z[3], 2) == 4);

	assert ($increment(s.x) == 1);
	assert ($increment(s.sy.y) == -1);
	assert ($increment(s.sy.y, 1) == -1);
	assert ($increment(s.sy.y, (1+1)) == 1);

	assert ($increment(s.sz.z) == 1);
	assert ($increment(s.sz.z, 1) == 1);
	assert ($increment(s.sz.z, 2) == -1);
	assert ($increment(s.sz.z, 3) == -1);
	assert ($increment(s.sz.z[3]) == -1);
	assert ($increment(s.sz.z[3][3]) == -1);
	assert ($increment(s.sz.z[3], 2) == -1);
end

endmodule
