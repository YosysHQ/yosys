// Certain arithmetic operations between a signal of width n and a constant can be directly mapped
// to a single k-LUT (where n <= k). This is preferable to normal alumacc techmapping process
// because for many targets, arithmetic techmapping creates hard logic (such as carry cells) which often
// cannot be optimized further.
//
// TODO: Currently, only comparisons with 1-bit output are mapped. Potentially, all arithmetic cells
// with n <= k inputs should be techmapped in this way, because this shortens the critical path
// from n to 1 by avoiding carry chains.

(* techmap_celltype = "$lt $le $gt $ge" *)
module _90_lut_cmp_ (A, B, Y);

parameter A_SIGNED = 0;
parameter B_SIGNED = 0;
parameter A_WIDTH = 0;
parameter B_WIDTH = 0;
parameter Y_WIDTH = 0;

input [A_WIDTH-1:0] A;
input [B_WIDTH-1:0] B;
output [Y_WIDTH-1:0] Y;

parameter _TECHMAP_CELLTYPE_ = "";

parameter _TECHMAP_CONSTMSK_A_ = 0;
parameter _TECHMAP_CONSTVAL_A_ = 0;
parameter _TECHMAP_CONSTMSK_B_ = 0;
parameter _TECHMAP_CONSTVAL_B_ = 0;

function automatic [(1 << `LUT_WIDTH)-1:0] gen_lut;
	input integer width;
	input integer operation;
	input integer swap;
	input integer sign;
	input integer operand;
	integer n, i_var, i_cst, lhs, rhs, o_bit;
	begin
		gen_lut = width'b0;
		for (n = 0; n < (1 << width); n++) begin
			if (sign)
				i_var = n[width-1:0];
			else
				i_var = n;
			i_cst = operand;
			if (swap) begin
				lhs = i_cst;
				rhs = i_var;
			end else begin
				lhs = i_var;
				rhs = i_cst;
			end
			if (operation == 0)
				o_bit = (lhs <  rhs);
			if (operation == 1)
				o_bit = (lhs <= rhs);
			if (operation == 2)
				o_bit = (lhs >  rhs);
			if (operation == 3)
				o_bit = (lhs >= rhs);
			if (operation == 4)
				o_bit = (lhs == rhs);
			if (operation == 5)
				o_bit = (lhs != rhs);
			gen_lut = gen_lut | (o_bit << n);
		end
	end
endfunction

generate
	if (_TECHMAP_CELLTYPE_ == "$lt")
		localparam operation = 0;
	if (_TECHMAP_CELLTYPE_ == "$le")
		localparam operation = 1;
	if (_TECHMAP_CELLTYPE_ == "$gt")
		localparam operation = 2;
	if (_TECHMAP_CELLTYPE_ == "$ge")
		localparam operation = 3;
	if (_TECHMAP_CELLTYPE_ == "$eq")
		localparam operation = 4;
	if (_TECHMAP_CELLTYPE_ == "$ne")
		localparam operation = 5;

	if (A_WIDTH > `LUT_WIDTH || B_WIDTH > `LUT_WIDTH || Y_WIDTH != 1)
		wire _TECHMAP_FAIL_ = 1;
	else if (&_TECHMAP_CONSTMSK_B_)
		\$lut #(
			.WIDTH(A_WIDTH),
			.LUT({ gen_lut(A_WIDTH, operation, 0, A_SIGNED && B_SIGNED, _TECHMAP_CONSTVAL_B_) })
		) _TECHMAP_REPLACE_ (
			.A(A),
			.Y(Y)
		);
	else if (&_TECHMAP_CONSTMSK_A_)
		\$lut #(
			.WIDTH(B_WIDTH),
			.LUT({ gen_lut(B_WIDTH, operation, 1, A_SIGNED && B_SIGNED, _TECHMAP_CONSTVAL_A_) })
		) _TECHMAP_REPLACE_ (
			.A(B),
			.Y(Y)
		);
	else
		wire _TECHMAP_FAIL_ = 1;
endgenerate

endmodule
