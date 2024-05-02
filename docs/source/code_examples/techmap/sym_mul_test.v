module test(A, B, C, Y1, Y2);
    input   [7:0] A, B, C;
    output  [7:0] Y1 = A * B;
    output [15:0] Y2 = A * C;
endmodule
