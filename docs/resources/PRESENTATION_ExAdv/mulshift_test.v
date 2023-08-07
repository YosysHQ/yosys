module test (A, X, Y);
input [7:0] A;
output [7:0] X = A * 8'd 6;
output [7:0] Y = A * 8'd 8;
endmodule
