
module test1(a, b, x, y);

input [7:0] a, b;
output [7:0] x, y;

inc #(.step(3)) inc_a (.in(a), .out(x));
inc #(.width(4), .step(7)) inc_b (b, y);

endmodule

// -----------------------------------

module test2(a, b, x, y);

input [7:0] a, b;
output [7:0] x, y;

inc #(5) inc_a (.in(a), .out(x));
inc #(4, 7) inc_b (b, y);

endmodule

// -----------------------------------

module inc(in, out);

parameter width = 8;
parameter step = 1;

input [width-1:0] in;
output [width-1:0] out;

assign out = in + step;

endmodule

