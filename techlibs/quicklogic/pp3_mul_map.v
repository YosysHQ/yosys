`default_nettype none

module __MUL32X32(A, B, Y);

parameter A_SIGNED = 1;
parameter B_SIGNED = 1;
parameter A_WIDTH = 32;
parameter B_WIDTH = 32;
parameter Y_WIDTH = 64;

input [A_WIDTH-1:0] A;
input [B_WIDTH-1:0] B;
output [Y_WIDTH-1:0] Y;

qlal4s3_mult_cell_macro _TECHMAP_REPLACE_ (
.Amult(A),
.Bmult(B),
.sel_mul_32x32(1'b1),
.Cmult(Y)
);

endmodule


module __MUL16X16(A, B, Y);

parameter A_SIGNED = 1;
parameter B_SIGNED = 1;
parameter A_WIDTH = 16;
parameter B_WIDTH = 16;
parameter Y_WIDTH = 32;

input [A_WIDTH-1:0] A;
input [B_WIDTH-1:0] B;
output [Y_WIDTH-1:0] Y;

qlal4s3_mult_cell_macro _TECHMAP_REPLACE_ (
.Amult(A),
.Bmult(B),
.sel_mul_32x32(1'b0),
.Cmult(Y)
);

endmodule