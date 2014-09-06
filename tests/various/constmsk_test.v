module test(input [3:0] A, output [3:0] Y1, Y2);
    assign Y1 = |{A[3], 1'b0, A[1]};
    assign Y2 = |{A[2], 1'b1, A[0]};
endmodule
