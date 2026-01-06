module \$__mul_wrapper (A, B, Y);

parameter A_SIGNED = 0;
parameter B_SIGNED = 0;
parameter A_WIDTH = 1;
parameter B_WIDTH = 1;
parameter Y_WIDTH = 1;

input [17:0] A;
input [24:0] B;
output [47:0] Y;

wire [A_WIDTH-1:0] A_ORIG = A;
wire [B_WIDTH-1:0] B_ORIG = B;
wire [Y_WIDTH-1:0] Y_ORIG;
assign Y = Y_ORIG;

\$mul #(
	.A_SIGNED(A_SIGNED),
	.B_SIGNED(B_SIGNED),
	.A_WIDTH(A_WIDTH),
	.B_WIDTH(B_WIDTH),
	.Y_WIDTH(Y_WIDTH)
) _TECHMAP_REPLACE_ (
	.A(A_ORIG),
	.B(B_ORIG),
	.Y(Y_ORIG)
);

endmodule

module \$__add_wrapper (A, B, Y);

parameter A_SIGNED = 0;
parameter B_SIGNED = 0;
parameter A_WIDTH = 1;
parameter B_WIDTH = 1;
parameter Y_WIDTH = 1;

input [47:0] A;
input [47:0] B;
output [47:0] Y;

wire [A_WIDTH-1:0] A_ORIG = A;
wire [B_WIDTH-1:0] B_ORIG = B;
wire [Y_WIDTH-1:0] Y_ORIG;
assign Y = Y_ORIG;

\$add #(
	.A_SIGNED(A_SIGNED),
	.B_SIGNED(B_SIGNED),
	.A_WIDTH(A_WIDTH),
	.B_WIDTH(B_WIDTH),
	.Y_WIDTH(Y_WIDTH)
) _TECHMAP_REPLACE_ (
	.A(A_ORIG),
	.B(B_ORIG),
	.Y(Y_ORIG)
);

endmodule
