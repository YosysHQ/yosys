module functions01;
wire [3:0]x;
wire [$size(x)-1:0]x_size;
wire [$size({x, x})-1:0]xx_size;
wire [3:0]y[0:5];
wire [$size(y)-1:0]y_size;
wire [3:0]z[0:5][0:7];
wire [$size(z)-1:0]z_size;

//
// The following are not supported yet:
//

//wire [$bits(x)-1:0]x_bits;
//wire [$bits({x, x})-1:0]xx_bits;

endmodule
