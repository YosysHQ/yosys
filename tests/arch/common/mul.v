module top
#(parameter X_WIDTH=6, Y_WIDTH=6, A_WIDTH=12)
(
    input [X_WIDTH-1:0] x,
    input [Y_WIDTH-1:0] y,

    output [A_WIDTH-1:0] A,
);
    assign A =  x * y;
endmodule
