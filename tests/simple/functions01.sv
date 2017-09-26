module functions01;
wire [3:0]x;
wire [$size(x)-1:0]x_size;
wire [$size({x, x})-1:0]xx_size;
wire [3:0]w[0:5];

//
// The following are not supported yet:
//

//wire [$size(w)-1:0]w_s;
//wire [$bits(x)-1:0]x_bits;
//wire [$bits({x, x})-1:0]xx_bits;

endmodule
