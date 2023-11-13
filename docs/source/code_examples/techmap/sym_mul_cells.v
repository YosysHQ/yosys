module MYMUL(A, B, Y);
    parameter WIDTH = 1;
    input [WIDTH-1:0] A, B;
    output [WIDTH-1:0] Y;
    assign Y = A * B;
endmodule
