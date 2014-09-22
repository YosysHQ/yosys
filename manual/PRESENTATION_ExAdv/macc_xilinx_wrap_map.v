(* techmap_celltype = "$mul" *)
module mul_wrap (A, B, Y);

parameter A_SIGNED = 0;
parameter B_SIGNED = 0;
parameter A_WIDTH = 1;
parameter B_WIDTH = 1;
parameter Y_WIDTH = 1;

input [A_WIDTH-1:0] A;
input [B_WIDTH-1:0] B;
output [Y_WIDTH-1:0] Y;

wire [17:0] A_18 = A;
wire [24:0] B_25 = B;
wire [47:0] Y_48;
assign Y = Y_48;

wire [1023:0] _TECHMAP_DO_ = "proc; clean";

reg _TECHMAP_FAIL_;
initial begin
	_TECHMAP_FAIL_ <= 0;
	if (A_SIGNED || B_SIGNED)
		_TECHMAP_FAIL_ <= 1;
	if (A_WIDTH < 4 || B_WIDTH < 4)
		_TECHMAP_FAIL_ <= 1;
	if (A_WIDTH > 18 || B_WIDTH > 25)
		_TECHMAP_FAIL_ <= 1;
	if (A_WIDTH*B_WIDTH < 100)
		_TECHMAP_FAIL_ <= 1;
end

\$__mul_wrapper #(
	.A_SIGNED(A_SIGNED),
	.B_SIGNED(B_SIGNED),
	.A_WIDTH(A_WIDTH),
	.B_WIDTH(B_WIDTH),
	.Y_WIDTH(Y_WIDTH)
) _TECHMAP_REPLACE_ (
	.A(A_18),
	.B(B_25),
	.Y(Y_48)
);

endmodule

(* techmap_celltype = "$add" *)
module add_wrap (A, B, Y);

parameter A_SIGNED = 0;
parameter B_SIGNED = 0;
parameter A_WIDTH = 1;
parameter B_WIDTH = 1;
parameter Y_WIDTH = 1;

input [A_WIDTH-1:0] A;
input [B_WIDTH-1:0] B;
output [Y_WIDTH-1:0] Y;

wire [47:0] A_48 = A;
wire [47:0] B_48 = B;
wire [47:0] Y_48;
assign Y = Y_48;

wire [1023:0] _TECHMAP_DO_ = "proc; clean";

reg _TECHMAP_FAIL_;
initial begin
	_TECHMAP_FAIL_ <= 0;
	if (A_SIGNED || B_SIGNED)
		_TECHMAP_FAIL_ <= 1;
	if (A_WIDTH < 10 && B_WIDTH < 10)
		_TECHMAP_FAIL_ <= 1;
end

\$__add_wrapper #(
	.A_SIGNED(A_SIGNED),
	.B_SIGNED(B_SIGNED),
	.A_WIDTH(A_WIDTH),
	.B_WIDTH(B_WIDTH),
	.Y_WIDTH(Y_WIDTH)
) _TECHMAP_REPLACE_ (
	.A(A_48),
	.B(B_48),
	.Y(Y_48)
);

endmodule
