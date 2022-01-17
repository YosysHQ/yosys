module top
(
    input [15:0] x,
    output A,
    output B
);
    assign A = &x;
    assign B = |x;
endmodule
