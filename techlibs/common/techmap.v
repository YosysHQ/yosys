/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 *  ---
 *
 *  The internal logic cell technology mapper.
 *
 *  This Verilog library contains the mapping of internal cells (e.g. $not with
 *  variable bit width) to the internal logic cells (such as the single bit $_NOT_
 *  gate). Usually this logic network is then mapped to the actual technology
 *  using e.g. the "abc" pass.
 *
 *  Note that this library does not map $mem cells. They must be mapped to logic
 *  and $dff cells using the "memory_map" pass first. (Or map it to custom cells,
 *  which is of course highly recommended for larger memories.)
 *
 */

`define MIN(_a, _b) ((_a) < (_b) ? (_a) : (_b))
`define MAX(_a, _b) ((_a) > (_b) ? (_a) : (_b))


// --------------------------------------------------------
// Use simplemap for trivial cell types
// --------------------------------------------------------

(* techmap_simplemap *)
(* techmap_celltype = "$not $and $or $xor $xnor" *)
module _90_simplemap_bool_ops;
endmodule

(* techmap_simplemap *)
(* techmap_celltype = "$reduce_and $reduce_or $reduce_xor $reduce_xnor $reduce_bool" *)
module _90_simplemap_reduce_ops;
endmodule

(* techmap_simplemap *)
(* techmap_celltype = "$logic_not $logic_and $logic_or" *)
module _90_simplemap_logic_ops;
endmodule

(* techmap_simplemap *)
(* techmap_celltype = "$eq $eqx $ne $nex" *)
module _90_simplemap_compare_ops;
endmodule

(* techmap_simplemap *)
(* techmap_celltype = "$buf $pos $slice $concat $mux $tribuf $bmux $bwmux $bweqx" *)
module _90_simplemap_various;
endmodule

(* techmap_simplemap *)
(* techmap_celltype = "$sr $ff $dff $dffe $adff $adffe $aldff $aldffe $sdff $sdffe $sdffce $dffsr $dffsre $dlatch $adlatch $dlatchsr" *)
module _90_simplemap_registers;
endmodule


// --------------------------------------------------------
// Shift operators
// --------------------------------------------------------

(* techmap_celltype = "$shr $shl $sshl $sshr" *)
module _90_shift_ops_shr_shl_sshl_sshr (A, B, Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	parameter _TECHMAP_CELLTYPE_ = "";
	localparam shift_left = _TECHMAP_CELLTYPE_ == "$shl" || _TECHMAP_CELLTYPE_ == "$sshl";
	localparam sign_extend = A_SIGNED && _TECHMAP_CELLTYPE_ == "$sshr";

	(* force_downto *)
	input [A_WIDTH-1:0] A;
	(* force_downto *)
	input [B_WIDTH-1:0] B;
	(* force_downto *)
	output [Y_WIDTH-1:0] Y;

	localparam WIDTH = `MAX(A_WIDTH, Y_WIDTH);
	localparam BB_WIDTH = `MIN($clog2(shift_left ? Y_WIDTH : A_SIGNED ? WIDTH : A_WIDTH) + 1, B_WIDTH);

	wire [1023:0] _TECHMAP_DO_00_ = "proc;;";
	wire [1023:0] _TECHMAP_DO_01_ = "RECURSION; CONSTMAP; opt_muxtree; opt_expr -mux_undef -mux_bool -fine;;;";

	integer i;
	(* force_downto *)
	reg [WIDTH-1:0] buffer;
	reg overflow;

	always @* begin
		overflow = B_WIDTH > BB_WIDTH ? |B[B_WIDTH-1:BB_WIDTH] : 1'b0;
		buffer = overflow ? {WIDTH{sign_extend ? A[A_WIDTH-1] : 1'b0}} : {{WIDTH-A_WIDTH{A_SIGNED ? A[A_WIDTH-1] : 1'b0}}, A};

		for (i = 0; i < BB_WIDTH; i = i+1)
			if (B[i]) begin
				if (shift_left)
					buffer = {buffer, (2**i)'b0};
				else if (2**i < WIDTH)
					buffer = {{2**i{sign_extend ? buffer[WIDTH-1] : 1'b0}}, buffer[WIDTH-1 : 2**i]};
				else
					buffer = {WIDTH{sign_extend ? buffer[WIDTH-1] : 1'b0}};
			end
	end

	assign Y = buffer;
endmodule

(* techmap_celltype = "$shift $shiftx" *)
module _90_shift_shiftx (A, B, Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	(* force_downto *)
	input [A_WIDTH-1:0] A;
	(* force_downto *)
	input [B_WIDTH-1:0] B;
	(* force_downto *)
	output [Y_WIDTH-1:0] Y;

	parameter _TECHMAP_CELLTYPE_ = "";
	parameter [B_WIDTH-1:0] _TECHMAP_CONSTMSK_B_ = 0;
	parameter [B_WIDTH-1:0] _TECHMAP_CONSTVAL_B_ = 0;

	localparam extbit = _TECHMAP_CELLTYPE_ == "$shift" ? 1'b0 : 1'bx;
	wire a_padding = _TECHMAP_CELLTYPE_ == "$shiftx" ? extbit : (A_SIGNED ? A[A_WIDTH-1] : 1'b0);

	localparam BB_WIDTH = `MIN($clog2(`MAX(A_WIDTH, Y_WIDTH)) + (B_SIGNED ? 2 : 1), B_WIDTH);
	localparam WIDTH = `MAX(A_WIDTH, Y_WIDTH) + (B_SIGNED ? 2**(BB_WIDTH-1) : 0);

	wire [1023:0] _TECHMAP_DO_00_ = "proc;;";
	wire [1023:0] _TECHMAP_DO_01_ = "CONSTMAP; opt_muxtree; opt_expr -mux_undef -mux_bool -fine;;;";

	integer i;
	(* force_downto *)
	reg [WIDTH-1:0] buffer;
	reg overflow;

	always @* begin
		overflow = 0;
		buffer = {WIDTH{extbit}};
		buffer[Y_WIDTH-1:0] = {Y_WIDTH{a_padding}};
		buffer[A_WIDTH-1:0] = A;

		if (B_WIDTH > BB_WIDTH) begin
			if (B_SIGNED) begin
				for (i = BB_WIDTH; i < B_WIDTH; i = i+1)
					if (B[i] != B[BB_WIDTH-1])
						overflow = 1;
			end else
				overflow = |B[B_WIDTH-1:BB_WIDTH];
			if (overflow)
				buffer = {WIDTH{extbit}};
		end

		if (B_SIGNED && B[BB_WIDTH-1])
			buffer = {buffer, {2**(BB_WIDTH-1){extbit}}};

		for (i = 0; i < (B_SIGNED ? BB_WIDTH-1 : BB_WIDTH); i = i+1)
			if (B[i]) begin
				if (2**i < WIDTH)
					buffer = {{2**i{extbit}}, buffer[WIDTH-1 : 2**i]};
				else
					buffer = {WIDTH{extbit}};
			end
	end
	assign Y = buffer;
endmodule


// --------------------------------------------------------
// Arithmetic operators
// --------------------------------------------------------

(* techmap_celltype = "$fa" *)
module _90_fa (A, B, C, X, Y);
	parameter WIDTH = 1;

	(* force_downto *)
	input [WIDTH-1:0] A, B, C;
	(* force_downto *)
	output [WIDTH-1:0] X, Y;

	(* force_downto *)
	wire [WIDTH-1:0] t1, t2, t3;

	assign t1 = A ^ B, t2 = A & B, t3 = C & t1;
	assign Y = t1 ^ C, X = t2 | t3;
endmodule

(* techmap_celltype = "$lcu" *)
module _90_lcu_brent_kung (P, G, CI, CO);
	parameter WIDTH = 2;

	(* force_downto *)
	input [WIDTH-1:0] P, G;
	input CI;

	(* force_downto *)
	output [WIDTH-1:0] CO;

	integer i, j;
	(* force_downto *)
	reg [WIDTH-1:0] p, g;

	wire [1023:0] _TECHMAP_DO_ = "proc; opt -fast";

	always @* begin
		p = P;
		g = G;

		// in almost all cases CI will be constant zero
		g[0] = g[0] | (p[0] & CI);

		// [[CITE]] Brent Kung Adder
		// R. P. Brent and H. T. Kung, "A Regular Layout for Parallel Adders",
		// IEEE Transaction on Computers, Vol. C-31, No. 3, p. 260-264, March, 1982

		// Main tree
		for (i = 1; i <= $clog2(WIDTH); i = i+1) begin
			for (j = 2**i - 1; j < WIDTH; j = j + 2**i) begin
				g[j] = g[j] | p[j] & g[j - 2**(i-1)];
				p[j] = p[j] & p[j - 2**(i-1)];
			end
		end

		// Inverse tree
		for (i = $clog2(WIDTH); i > 0; i = i-1) begin
			for (j = 2**i + 2**(i-1) - 1; j < WIDTH; j = j + 2**i) begin
				g[j] = g[j] | p[j] & g[j - 2**(i-1)];
				p[j] = p[j] & p[j - 2**(i-1)];
			end
		end
	end

	assign CO = g;
endmodule

(* techmap_celltype = "$alu" *)
module _90_alu (A, B, CI, BI, X, Y, CO);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	(* force_downto *)
	input [A_WIDTH-1:0] A;
	(* force_downto *)
	input [B_WIDTH-1:0] B;
	(* force_downto *)
	output [Y_WIDTH-1:0] X, Y;

	input CI, BI;
	(* force_downto *)
	output [Y_WIDTH-1:0] CO;

	(* force_downto *)
	wire [Y_WIDTH-1:0] AA = A_buf;
	(* force_downto *)
	wire [Y_WIDTH-1:0] BB = BI ? ~B_buf : B_buf;

	(* force_downto *)
	wire [Y_WIDTH-1:0] A_buf, B_buf;
	\$pos #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(Y_WIDTH)) A_conv (.A(A), .Y(A_buf));
	\$pos #(.A_SIGNED(B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(Y_WIDTH)) B_conv (.A(B), .Y(B_buf));

	\$lcu #(.WIDTH(Y_WIDTH)) lcu (.P(X), .G(AA & BB), .CI(CI), .CO(CO));

	assign X = AA ^ BB;
	assign Y = X ^ {CO, CI};
endmodule

(* techmap_maccmap *)
(* techmap_celltype = "$macc $macc_v2" *)
module _90_macc;
endmodule

(* techmap_wrap = "alumacc" *)
(* techmap_celltype = "$lt $le $ge $gt $add $sub $neg $mul" *)
module _90_alumacc;
endmodule


// --------------------------------------------------------
// Divide and Modulo
// --------------------------------------------------------

`ifndef NODIV
module \$__div_mod_u (A, B, Y, R);
	parameter WIDTH = 1;

	(* force_downto *)
	input [WIDTH-1:0] A, B;
	(* force_downto *)
	output [WIDTH-1:0] Y, R;

	(* force_downto *)
	wire [WIDTH*WIDTH-1:0] chaindata;
	assign R = chaindata[WIDTH*WIDTH-1:WIDTH*(WIDTH-1)];

	genvar i;
	generate begin
		for (i = 0; i < WIDTH; i=i+1) begin:stage
			(* force_downto *)
			wire [WIDTH-1:0] stage_in;

			if (i == 0) begin:cp
				assign stage_in = A;
			end else begin:cp
				assign stage_in = chaindata[i*WIDTH-1:(i-1)*WIDTH];
			end

			assign Y[WIDTH-(i+1)] = stage_in >= {B, {WIDTH-(i+1){1'b0}}};
			assign chaindata[(i+1)*WIDTH-1:i*WIDTH] = Y[WIDTH-(i+1)] ? stage_in - {B, {WIDTH-(i+1){1'b0}}} : stage_in;
		end
	end endgenerate
endmodule

// truncating signed division/modulo
module \$__div_mod_trunc (A, B, Y, R);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	localparam WIDTH =
			A_WIDTH >= B_WIDTH && A_WIDTH >= Y_WIDTH ? A_WIDTH :
			B_WIDTH >= A_WIDTH && B_WIDTH >= Y_WIDTH ? B_WIDTH : Y_WIDTH;

	(* force_downto *)
	input [A_WIDTH-1:0] A;
	(* force_downto *)
	input [B_WIDTH-1:0] B;
	(* force_downto *)
	output [Y_WIDTH-1:0] Y, R;

	(* force_downto *)
	wire [WIDTH-1:0] A_buf, B_buf;
	\$pos #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(WIDTH)) A_conv (.A(A), .Y(A_buf));
	\$pos #(.A_SIGNED(B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(WIDTH)) B_conv (.A(B), .Y(B_buf));

	(* force_downto *)
	wire [WIDTH-1:0] A_buf_u, B_buf_u, Y_u, R_u;
	assign A_buf_u = A_SIGNED && A_buf[WIDTH-1] ? -A_buf : A_buf;
	assign B_buf_u = B_SIGNED && B_buf[WIDTH-1] ? -B_buf : B_buf;

	\$__div_mod_u #(
		.WIDTH(WIDTH)
	) div_mod_u (
		.A(A_buf_u),
		.B(B_buf_u),
		.Y(Y_u),
		.R(R_u)
	);

	assign Y = A_SIGNED && B_SIGNED && (A_buf[WIDTH-1] != B_buf[WIDTH-1]) ? -Y_u : Y_u;
	assign R = A_SIGNED && B_SIGNED && A_buf[WIDTH-1] ? -R_u : R_u;
endmodule

(* techmap_celltype = "$div" *)
module _90_div (A, B, Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	(* force_downto *)
	input [A_WIDTH-1:0] A;
	(* force_downto *)
	input [B_WIDTH-1:0] B;
	(* force_downto *)
	output [Y_WIDTH-1:0] Y;

	\$__div_mod_trunc #(
		.A_SIGNED(A_SIGNED),
		.B_SIGNED(B_SIGNED),
		.A_WIDTH(A_WIDTH),
		.B_WIDTH(B_WIDTH),
		.Y_WIDTH(Y_WIDTH)
	) div_mod (
		.A(A),
		.B(B),
		.Y(Y)
	);
endmodule

(* techmap_celltype = "$mod" *)
module _90_mod (A, B, Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	(* force_downto *)
	input [A_WIDTH-1:0] A;
	(* force_downto *)
	input [B_WIDTH-1:0] B;
	(* force_downto *)
	output [Y_WIDTH-1:0] Y;

	\$__div_mod_trunc #(
		.A_SIGNED(A_SIGNED),
		.B_SIGNED(B_SIGNED),
		.A_WIDTH(A_WIDTH),
		.B_WIDTH(B_WIDTH),
		.Y_WIDTH(Y_WIDTH)
	) div_mod (
		.A(A),
		.B(B),
		.R(Y)
	);
endmodule

// flooring signed division/modulo
module \$__div_mod_floor (A, B, Y, R);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	localparam WIDTH =
			A_WIDTH >= B_WIDTH && A_WIDTH >= Y_WIDTH ? A_WIDTH :
			B_WIDTH >= A_WIDTH && B_WIDTH >= Y_WIDTH ? B_WIDTH : Y_WIDTH;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] Y, R;

	wire [WIDTH-1:0] A_buf, B_buf;
	\$pos #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(WIDTH)) A_conv (.A(A), .Y(A_buf));
	\$pos #(.A_SIGNED(B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(WIDTH)) B_conv (.A(B), .Y(B_buf));

	wire [WIDTH-1:0] A_buf_u, B_buf_u, Y_u, R_u, R_s;
	assign A_buf_u = A_SIGNED && A_buf[WIDTH-1] ? -A_buf : A_buf;
	assign B_buf_u = B_SIGNED && B_buf[WIDTH-1] ? -B_buf : B_buf;

	\$__div_mod_u #(
		.WIDTH(WIDTH)
	) div_mod_u (
		.A(A_buf_u),
		.B(B_buf_u),
		.Y(Y_u),
		.R(R_u)
	);

	// For negative results, if there was a remainder, subtract one to turn
	// the round towards 0 into a round towards -inf
	assign Y = A_SIGNED && B_SIGNED && (A_buf[WIDTH-1] != B_buf[WIDTH-1]) ? (R_u == 0 ? -Y_u : -Y_u-1) : Y_u;

	// truncating modulo
	assign R_s = A_SIGNED && B_SIGNED && A_buf[WIDTH-1] ? -R_u : R_u;
	// Flooring modulo differs from truncating modulo only if it is nonzero and
	// A and B have different signs - then `floor - trunc = B`
	assign R = (R_s != 0) && A_SIGNED && B_SIGNED && (A_buf[WIDTH-1] != B_buf[WIDTH-1]) ? $signed(B_buf) + $signed(R_s) : R_s;
endmodule

(* techmap_celltype = "$divfloor" *)
module _90_divfloor (A, B, Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	(* force_downto *)
	input [A_WIDTH-1:0] A;
	(* force_downto *)
	input [B_WIDTH-1:0] B;
	(* force_downto *)
	output [Y_WIDTH-1:0] Y;

	\$__div_mod_floor #(
		.A_SIGNED(A_SIGNED),
		.B_SIGNED(B_SIGNED),
		.A_WIDTH(A_WIDTH),
		.B_WIDTH(B_WIDTH),
		.Y_WIDTH(Y_WIDTH)
	) div_mod (
		.A(A),
		.B(B),
		.Y(Y)
	);
endmodule

(* techmap_celltype = "$modfloor" *)
module _90_modfloor (A, B, Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	(* force_downto *)
	input [A_WIDTH-1:0] A;
	(* force_downto *)
	input [B_WIDTH-1:0] B;
	(* force_downto *)
	output [Y_WIDTH-1:0] Y;

	\$__div_mod_floor #(
		.A_SIGNED(A_SIGNED),
		.B_SIGNED(B_SIGNED),
		.A_WIDTH(A_WIDTH),
		.B_WIDTH(B_WIDTH),
		.Y_WIDTH(Y_WIDTH)
	) div_mod (
		.A(A),
		.B(B),
		.R(Y)
	);
endmodule
`endif

// --------------------------------------------------------
// Power
// --------------------------------------------------------

(* techmap_celltype = "$pow" *)
module _90_pow (A, B, Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	(* force_downto *)
	input [A_WIDTH-1:0] A;
	(* force_downto *)
	input [B_WIDTH-1:0] B;
	(* force_downto *)
	output [Y_WIDTH-1:0] Y;

	wire _TECHMAP_FAIL_ = 1;
endmodule


// --------------------------------------------------------
// Parallel Multiplexers
// --------------------------------------------------------

(* techmap_celltype = "$pmux" *)
module _90_pmux (A, B, S, Y);
	parameter WIDTH = 1;
	parameter S_WIDTH = 1;

	(* force_downto *)
	input [WIDTH-1:0] A;
	(* force_downto *)
	input [WIDTH*S_WIDTH-1:0] B;
	(* force_downto *)
	input [S_WIDTH-1:0] S;
	(* force_downto *)
	output [WIDTH-1:0] Y;

	(* force_downto *)
	wire [WIDTH-1:0] Y_B;

	genvar i, j;
	generate
		(* force_downto *)
		wire [WIDTH*S_WIDTH-1:0] B_AND_S;
		for (i = 0; i < S_WIDTH; i = i + 1) begin:B_AND
			assign B_AND_S[WIDTH*(i+1)-1:WIDTH*i] = B[WIDTH*(i+1)-1:WIDTH*i] & {WIDTH{S[i]}};
		end:B_AND
		for (i = 0; i < WIDTH; i = i + 1) begin:B_OR
			(* force_downto *)
			wire [S_WIDTH-1:0] B_AND_BITS;
			for (j = 0; j < S_WIDTH; j = j + 1) begin:B_AND_BITS_COLLECT
				assign B_AND_BITS[j] = B_AND_S[WIDTH*j+i];
			end:B_AND_BITS_COLLECT
			assign Y_B[i] = |B_AND_BITS;
		end:B_OR
	endgenerate

	assign Y = |S ? Y_B : A;
endmodule

// --------------------------------------------------------
// Demultiplexers
// --------------------------------------------------------

(* techmap_celltype = "$demux" *)
module _90_demux (A, S, Y);
	parameter WIDTH = 1;
	parameter S_WIDTH = 1;

	(* force_downto *)
	input [WIDTH-1:0] A;
	(* force_downto *)
	input [S_WIDTH-1:0] S;
	(* force_downto *)
	output [(WIDTH << S_WIDTH)-1:0] Y;

	generate
		if (S_WIDTH == 0) begin
			assign Y = A;
		end else if (S_WIDTH == 1) begin
			assign Y[0+:WIDTH] = S ? 0 : A;
			assign Y[WIDTH+:WIDTH] = S ? A : 0;
		end else begin
			localparam SPLIT = S_WIDTH / 2;
			wire [(1 << (S_WIDTH-SPLIT))-1:0] YH;
			wire [(1 << SPLIT)-1:0] YL;
			$demux #(.WIDTH(1), .S_WIDTH(SPLIT)) lo (.A(1'b1), .S(S[SPLIT-1:0]), .Y(YL));
			$demux #(.WIDTH(1), .S_WIDTH(S_WIDTH-SPLIT)) hi (.A(1'b1), .S(S[S_WIDTH-1:SPLIT]), .Y(YH));
			genvar i;
			for (i = 0; i < (1 << S_WIDTH); i = i + 1) begin
				localparam [S_WIDTH-1:0] IDX = i;
				assign Y[i*WIDTH+:WIDTH] = (YL[IDX[SPLIT-1:0]] & YH[IDX[S_WIDTH-1:SPLIT]]) ? A : 0;
			end
		end
	endgenerate
endmodule


// --------------------------------------------------------
// LUTs
// --------------------------------------------------------

`ifndef NOLUT
(* techmap_simplemap *)
(* techmap_celltype = "$lut $sop" *)
module _90_lut;
endmodule
`endif

