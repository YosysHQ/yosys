`default_nettype none

module __MUL27X27(A, B, Y);

parameter A_SIGNED = 1;
parameter B_SIGNED = 1;
parameter A_WIDTH = 27;
parameter B_WIDTH = 27;
parameter Y_WIDTH = 54;

input [A_WIDTH-1:0] A;
input [B_WIDTH-1:0] B;
output [Y_WIDTH-1:0] Y;

MISTRAL_MUL27X27 _TECHMAP_REPLACE_ (.A(A), .B(B), .Y(Y));

endmodule


module __MUL18X18(A, B, Y);

parameter A_SIGNED = 1;
parameter B_SIGNED = 1;
parameter A_WIDTH = 18;
parameter B_WIDTH = 18;
parameter Y_WIDTH = 36;

input [A_WIDTH-1:0] A;
input [B_WIDTH-1:0] B;
output [Y_WIDTH-1:0] Y;

MISTRAL_MUL18X18 _TECHMAP_REPLACE_ (.A(A), .B(B), .Y(Y));

endmodule


module __MUL9X9(A, B, Y);

parameter A_SIGNED = 1;
parameter B_SIGNED = 1;
parameter A_WIDTH = 9;
parameter B_WIDTH = 9;
parameter Y_WIDTH = 18;

input [A_WIDTH-1:0] A;
input [B_WIDTH-1:0] B;
output [Y_WIDTH-1:0] Y;

MISTRAL_MUL9X9 _TECHMAP_REPLACE_ (.A(A), .B(B), .Y(Y));

endmodule
