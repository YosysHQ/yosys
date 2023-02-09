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

assert property ($size(s) == $size(s.t) + $size(s.x) + $size(s.sy) + $size(s.sz));
assert property ($size(s) == 1 + 4 + 6*4 + 6*8*4);

assert property ($size(t) == 1);
assert property ($size(s.x) == 4);
assert property ($size({3{s.x}}) == 3*4);
assert property ($size(s.sy.y) == 6);
assert property ($size(s.sy.y, 1) == 6);
assert property ($size(s.sy.y, (1+1)) == 4);
assert property ($size(s.sy.y[2], 1) == 4);
// This is unsupported at the moment
//assert property ($size(s.sy.y[2][1], 1) == 1);

assert property ($size(s.sz.z) == 6);
assert property ($size(s.sz.z, 1) == 6);
assert property ($size(s.sz.z, 2) == 8);
assert property ($size(s.sz.z, 3) == 4);
assert property ($size(s.sz.z[3], 1) == 8);
assert property ($size(s.sz.z[3][3], 1) == 4);
// This is unsupported at the moment
//assert property ($size(s.sz.z[3][3][3], 1) == 1);
// This should trigger an error if enabled (it does).
//assert property ($size(s.sz.z, 4) == 4);

//wire [$bits(s.x)-1:0]x_bits;
//wire [$bits({s.x, s.x})-1:0]xx_bits;

assert property ($bits(t) == 1);
assert property ($bits(s.x) == 4);
assert property ($bits(s.sy.y) == 4*6);
assert property ($bits(s.sz.z) == 4*6*8);

assert property ($high(s.x) == 5);
assert property ($high(s.sy.y) == 7);
assert property ($high(s.sy.y, 1) == 7);
assert property ($high(s.sy.y, (1+1)) == 3);

assert property ($high(s.sz.z) == 7);
assert property ($high(s.sz.z, 1) == 7);
assert property ($high(s.sz.z, 2) == 9);
assert property ($high(s.sz.z, 3) == 4);
assert property ($high(s.sz.z[3]) == 9);
assert property ($high(s.sz.z[3][3]) == 4);
assert property ($high(s.sz.z[3], 2) == 4);

assert property ($low(s.x) == 2);
assert property ($low(s.sy.y) == 2);
assert property ($low(s.sy.y, 1) == 2);
assert property ($low(s.sy.y, (1+1)) == 0);

assert property ($low(s.sz.z) == 2);
assert property ($low(s.sz.z, 1) == 2);
assert property ($low(s.sz.z, 2) == 2);
assert property ($low(s.sz.z, 3) == 1);
assert property ($low(s.sz.z[3]) == 2);
assert property ($low(s.sz.z[3][3]) == 1);
assert property ($low(s.sz.z[3], 2) == 1);

assert property ($left(s.x) == 5);
assert property ($left(s.sy.y) == 2);
assert property ($left(s.sy.y, 1) == 2);
assert property ($left(s.sy.y, (1+1)) == 3);

assert property ($left(s.sz.z) == 7);
assert property ($left(s.sz.z, 1) == 7);
assert property ($left(s.sz.z, 2) == 2);
assert property ($left(s.sz.z, 3) == 1);
assert property ($left(s.sz.z[3]) == 2);
assert property ($left(s.sz.z[3][3]) == 1);
assert property ($left(s.sz.z[3], 2) == 1);

assert property ($right(s.x) == 2);
assert property ($right(s.sy.y) == 7);
assert property ($right(s.sy.y, 1) == 7);
assert property ($right(s.sy.y, (1+1)) == 0);

assert property ($right(s.sz.z) == 2);
assert property ($right(s.sz.z, 1) == 2);
assert property ($right(s.sz.z, 2) == 9);
assert property ($right(s.sz.z, 3) == 4);
assert property ($right(s.sz.z[3]) == 9);
assert property ($right(s.sz.z[3][3]) == 4);
assert property ($right(s.sz.z[3], 2) == 4);
endmodule
