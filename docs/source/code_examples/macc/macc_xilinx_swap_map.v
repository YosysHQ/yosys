(* techmap_celltype = "$mul" *)
module mul_swap_ports (A, B, Y);

parameter A_SIGNED = 0;
parameter B_SIGNED = 0;
parameter A_WIDTH = 1;
parameter B_WIDTH = 1;
parameter Y_WIDTH = 1;

input [A_WIDTH-1:0] A;
input [B_WIDTH-1:0] B;
output [Y_WIDTH-1:0] Y;

wire _TECHMAP_FAIL_ = A_WIDTH <= B_WIDTH;

\$mul #(
	.A_SIGNED(B_SIGNED),
	.B_SIGNED(A_SIGNED),
	.A_WIDTH(B_WIDTH),
	.B_WIDTH(A_WIDTH),
	.Y_WIDTH(Y_WIDTH)
) _TECHMAP_REPLACE_ (
	.A(B),
	.B(A),
	.Y(Y)
);

endmodule
