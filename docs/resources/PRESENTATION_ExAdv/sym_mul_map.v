module \$mul (A, B, Y);
    parameter A_SIGNED = 0;
    parameter B_SIGNED = 0;
    parameter A_WIDTH = 1;
    parameter B_WIDTH = 1;
    parameter Y_WIDTH = 1;

    input [A_WIDTH-1:0] A;
    input [B_WIDTH-1:0] B;
    output [Y_WIDTH-1:0] Y;

    wire _TECHMAP_FAIL_ = A_WIDTH != B_WIDTH || B_WIDTH != Y_WIDTH;

    MYMUL #( .WIDTH(Y_WIDTH) ) g ( .A(A), .B(B), .Y(Y) );
endmodule
