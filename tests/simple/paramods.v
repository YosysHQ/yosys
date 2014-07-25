
module pm_test1(a, b, x, y);

input [7:0] a, b;
output [7:0] x, y;

inc #(.step(3)) inc_a (.in(a), .out(x));
inc #(.width(4), .step(7)) inc_b (b, y);

endmodule

// -----------------------------------

module pm_test2(a, b, x, y);

input [7:0] a, b;
output [7:0] x, y;

inc #(5) inc_a (.in(a), .out(x));
inc #(4, 7) inc_b (b, y);

endmodule

// -----------------------------------

module pm_test3(a, b, x, y);

input [7:0] a, b;
output [7:0] x, y;

inc inc_a (.in(a), .out(x));
inc inc_b (b, y);

defparam inc_a.step = 3;
defparam inc_b.step = 7;
defparam inc_b.width = 4;

endmodule

// -----------------------------------

module inc(in, out);

parameter width = 8;
parameter step = 1;

input [width-1:0] in;
output [width-1:0] out;

assign out = in + step;

endmodule

