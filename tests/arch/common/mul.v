module top
(
    input [5:0] x,
    input [5:0] y,

    output [11:0] A,
);
    assign A =  x * y;
endmodule
