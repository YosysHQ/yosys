module test (A, B, X, Y);
input [7:0] A, B;
output [7:0] X = A + B;
output [7:0] Y = A + A;
endmodule
