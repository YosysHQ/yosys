module test_arith(
    input [7:0] a,
    input [7:0] b,
    output [7:0] add,
    output [0:0] add_cout,
    output [7:0] minus,
    output [0:0] minus_cout,
    output threshold
);

parameter INCREMENT = 8;
parameter THRESHOLD = 16;

assign {add_cout, add} = a + b;
assign {minus_cout, minus} = a - b;
assign threshold = (a + INCREMENT) >= THRESHOLD;

endmodule
