module functions01;

wire t;
wire [5:2]x;
wire [3:0]y[2:7];
wire [3:0]z[7:2][2:9];

//wire [$size(x)-1:0]x_size;
//wire [$size({x, x})-1:0]xx_size;
//wire [$size(y)-1:0]y_size;
//wire [$size(z)-1:0]z_size;

assert property ($size(t) == 1);
assert property ($size(x) == 4);
assert property ($size({3{x}}) == 3*4);
assert property ($size(y) == 6);
assert property ($size(y, 1) == 6);
assert property ($size(y, (1+1)) == 4);
// This is unsupported at the moment
//assert property ($size(y[2], 1) == 4);
//assert property ($size(y[2][1], 1) == 1);

assert property ($size(z) == 6);
assert property ($size(z, 1) == 6);
assert property ($size(z, 2) == 8);
assert property ($size(z, 3) == 4);
// This is unsupported at the moment
assert property ($size(z[3], 1) == 8);
assert property ($size(z[3][3], 1) == 4);
//assert property ($size(z[3][3][3], 1) == 1);
// This should trigger an error if enabled (it does).
//assert property ($size(z, 4) == 4);

//wire [$bits(x)-1:0]x_bits;
//wire [$bits({x, x})-1:0]xx_bits;

assert property ($bits(t) == 1);
assert property ($bits(x) == 4);
assert property ($bits(y) == 4*6);
assert property ($bits(z) == 4*6*8);

assert property ($high(x) == 5);
assert property ($high(y) == 7);
assert property ($high(y, 1) == 7);
assert property ($high(y, (1+1)) == 3);

assert property ($high(z) == 7);
assert property ($high(z, 1) == 7);
assert property ($high(z, 2) == 9);
assert property ($high(z, 3) == 3);
assert property ($high(z[3]) == 9);
assert property ($high(z[3][3]) == 3);
assert property ($high(z[3], 2) == 3);

assert property ($low(x) == 2);
assert property ($low(y) == 2);
assert property ($low(y, 1) == 2);
assert property ($low(y, (1+1)) == 0);

assert property ($low(z) == 2);
assert property ($low(z, 1) == 2);
assert property ($low(z, 2) == 2);
assert property ($low(z, 3) == 0);
assert property ($low(z[3]) == 2);
assert property ($low(z[3][3]) == 0);
assert property ($low(z[3], 2) == 0);

assert property ($left(x) == 5);
assert property ($left(y) == 2);
assert property ($left(y, 1) == 2);
assert property ($left(y, (1+1)) == 3);

assert property ($left(z) == 7);
assert property ($left(z, 1) == 7);
assert property ($left(z, 2) == 2);
assert property ($left(z, 3) == 3);
assert property ($left(z[3]) == 2);
assert property ($left(z[3][3]) == 3);
assert property ($left(z[3], 2) == 3);

assert property ($right(x) == 2);
assert property ($right(y) == 7);
assert property ($right(y, 1) == 7);
assert property ($right(y, (1+1)) == 0);

assert property ($right(z) == 2);
assert property ($right(z, 1) == 2);
assert property ($right(z, 2) == 9);
assert property ($right(z, 3) == 0);
assert property ($right(z[3]) == 9);
assert property ($right(z[3][3]) == 0);
assert property ($right(z[3], 2) == 0);
endmodule
