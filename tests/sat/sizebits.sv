module functions01;

wire [5:2]x;
wire [3:0]y[2:7];
wire [3:0]z[7:2][2:9];

//wire [$size(x)-1:0]x_size;
//wire [$size({x, x})-1:0]xx_size;
//wire [$size(y)-1:0]y_size;
//wire [$size(z)-1:0]z_size;

assert property ($size(x) == 4);
assert property ($size({3{x}}) == 3*4);
assert property ($size(y) == 6);
assert property ($size(y, 1) == 6);
assert property ($size(y, (1+1)) == 4);

assert property ($size(z) == 6);
assert property ($size(z, 1) == 6);
assert property ($size(z, 2) == 8);
assert property ($size(z, 3) == 4);
// This should trigger an error if enabled (it does).
//assert property ($size(z, 4) == 4);

//wire [$bits(x)-1:0]x_bits;
//wire [$bits({x, x})-1:0]xx_bits;

assert property ($bits(x) == 4);
assert property ($bits(y) == 4*6);
assert property ($bits(z) == 4*6*8);

endmodule
