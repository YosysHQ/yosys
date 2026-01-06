module constgtge(C, A, B, Y);
parameter A_WIDTH = 0;
parameter B_WIDTH = 0;

(* force_downto *)
input [A_WIDTH-1:0] A;
(* force_downto *)
input [B_WIDTH-1:0] B;
output Y;
input C;

wire [A_WIDTH:0] ch;
genvar n;
generate
	if (B_WIDTH > A_WIDTH) begin
		// Fail
	end else begin
		assign ch[0] = C;
		for (n = 0; n < A_WIDTH; n = n + 1) begin
			if (n < B_WIDTH) begin
				assign ch[n + 1] = B[n] ? (ch[n] && A[n]) : (ch[n] || A[n]);
			end else begin
				assign ch[n + 1] = ch[n] || A[n];
			end
		end
		assign Y = ch[A_WIDTH];
	end
endgenerate
endmodule

module constltle(C, A, B, Y);
parameter A_WIDTH = 0;
parameter B_WIDTH = 0;

(* force_downto *)
input [A_WIDTH-1:0] A;
(* force_downto *)
input [B_WIDTH-1:0] B;
output Y;
input C;

wire [A_WIDTH:0] ch;
genvar n;
generate
	if (B_WIDTH > A_WIDTH) begin
		// Fail
	end else begin
		assign ch[0] = C;
		for (n = 0; n < A_WIDTH; n = n + 1) begin
			if (n < B_WIDTH) begin
				assign ch[n + 1] = !B[n] ? (ch[n] && !A[n]) : (ch[n] || !A[n]);
			end else begin
				assign ch[n + 1] = ch[n] && !A[n];
			end
		end
		assign Y = ch[A_WIDTH];
	end
endgenerate
endmodule

(* techmap_celltype = "$ge $gt $le $lt" *)
module _map_const_cmp_(A, B, Y);
parameter A_WIDTH = 0;
parameter B_WIDTH = 0;
parameter Y_WIDTH = 0;
parameter A_SIGNED = 0;
parameter B_SIGNED = 0;

(* force_downto *)
input [A_WIDTH-1:0] A;
(* force_downto *)
input [B_WIDTH-1:0] B;
(* force_downto *)
output [Y_WIDTH-1:0] Y;

parameter _TECHMAP_CELLTYPE_ = "";

parameter _TECHMAP_CONSTMSK_A_ = 0;
parameter _TECHMAP_CONSTVAL_A_ = 0;
parameter _TECHMAP_CONSTMSK_B_ = 0;
parameter _TECHMAP_CONSTVAL_B_ = 0;

wire [1023:0] _TECHMAP_DO_ = "opt -fast;";

wire [A_WIDTH:0] ch;

genvar n;
generate
	if (Y_WIDTH != 1 || A_SIGNED || B_SIGNED)
		wire _TECHMAP_FAIL_ = 1;
	else if (&_TECHMAP_CONSTMSK_A_) begin
		if (A_WIDTH > B_WIDTH)
			wire _TECHMAP_FAIL_ = 1;
		else if (_TECHMAP_CELLTYPE_ == "$lt" || _TECHMAP_CELLTYPE_ == "$le")
			constgtge #(.A_WIDTH(B_WIDTH), .B_WIDTH(A_WIDTH))
				_TECHMAP_REPLACE_(.A(B), .B(A), .Y(Y),
					.C(_TECHMAP_CELLTYPE_ == "$lt"));
		else
			constltle #(.A_WIDTH(B_WIDTH), .B_WIDTH(A_WIDTH))
				_TECHMAP_REPLACE_(.A(B), .B(A), .Y(Y),
					.C(_TECHMAP_CELLTYPE_ == "$gt"));
	end else if (&_TECHMAP_CONSTMSK_B_) begin
		if (B_WIDTH > A_WIDTH)
			wire _TECHMAP_FAIL_ = 1;
		else if (_TECHMAP_CELLTYPE_ == "$lt" || _TECHMAP_CELLTYPE_ == "$le")
			constltle #(.A_WIDTH(A_WIDTH), .B_WIDTH(B_WIDTH))
				_TECHMAP_REPLACE_(.A(A), .B(B), .Y(Y),
					.C(_TECHMAP_CELLTYPE_ == "$le"));
		else
			constgtge #(.A_WIDTH(A_WIDTH), .B_WIDTH(B_WIDTH))
				_TECHMAP_REPLACE_(.A(A), .B(B), .Y(Y),
					.C(_TECHMAP_CELLTYPE_ == "$ge"));
	end else
		wire _TECHMAP_FAIL_ = 1;
endgenerate

endmodule
