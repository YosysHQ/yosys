// A comparison against a constant does not need a generic (carry-chain) comparator: each
// constant bit decides whether the running result is extended with an AND or an OR of the
// corresponding variable bit, so the whole compare folds into an AND/OR chain that
// downstream logic optimization can rebalance into log depth.

// Y = (A >= B) when C is 1, (A > B) when C is 0. B is expected to be constant, which folds
// each mux below into a single AND (for B[n] = 1) or OR (for B[n] = 0).
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

// Y = (A <= B) when C is 1, (A < B) when C is 0: constgtge over inverted operands.
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

// The comparison is signed only when both operands are; mixed signedness is unsigned
localparam SGN = A_SIGNED && B_SIGNED;
// Compare at the wider width, so either operand may be the narrower one
localparam W = A_WIDTH > B_WIDTH ? A_WIDTH : B_WIDTH;

wire [W-1:0] Aext, Bext, bias, Ab, Bb;

generate
	if (SGN) begin
		// Flipping the sign bit turns two's-complement order into unsigned order, so the
		// unsigned chains below cover signed compares too
		assign Aext = $signed(A);
		assign Bext = $signed(B);
		assign bias = 1 << (W - 1);
	end else begin
		assign Aext = A;
		assign Bext = B;
		assign bias = 0;
	end
endgenerate

assign Ab = Aext ^ bias;
assign Bb = Bext ^ bias;

generate
	if (Y_WIDTH != 1)
		wire _TECHMAP_FAIL_ = 1;
	else if (&_TECHMAP_CONSTMSK_B_) begin
		if (_TECHMAP_CELLTYPE_ == "$lt" || _TECHMAP_CELLTYPE_ == "$le")
			constltle #(.A_WIDTH(W), .B_WIDTH(W))
				_TECHMAP_REPLACE_(.A(Ab), .B(Bb), .Y(Y),
					.C(_TECHMAP_CELLTYPE_ == "$le"));
		else
			constgtge #(.A_WIDTH(W), .B_WIDTH(W))
				_TECHMAP_REPLACE_(.A(Ab), .B(Bb), .Y(Y),
					.C(_TECHMAP_CELLTYPE_ == "$ge"));
	end else if (&_TECHMAP_CONSTMSK_A_) begin
		// Constant on A: swap the operands and mirror the operator, as A < B is B > A
		if (_TECHMAP_CELLTYPE_ == "$lt" || _TECHMAP_CELLTYPE_ == "$le")
			constgtge #(.A_WIDTH(W), .B_WIDTH(W))
				_TECHMAP_REPLACE_(.A(Bb), .B(Ab), .Y(Y),
					.C(_TECHMAP_CELLTYPE_ == "$le"));
		else
			constltle #(.A_WIDTH(W), .B_WIDTH(W))
				_TECHMAP_REPLACE_(.A(Bb), .B(Ab), .Y(Y),
					.C(_TECHMAP_CELLTYPE_ == "$ge"));
	end else
		wire _TECHMAP_FAIL_ = 1;
endgenerate

endmodule
