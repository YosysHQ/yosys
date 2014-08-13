/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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
 *  This verilog library contains the mapping of internal cells (e.g. $not with
 *  variable bit width) to the internal logic cells (such as the single bit $_INV_ 
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
(* techmap_celltype = "$pos $bu0" *)
module simplemap_buffers;
endmodule

(* techmap_simplemap *)
(* techmap_celltype = "$not $and $or $xor $xnor" *)
module simplemap_bool_ops;
endmodule

(* techmap_simplemap *)
(* techmap_celltype = "$reduce_and $reduce_or $reduce_xor $reduce_xnor $reduce_bool" *)
module simplemap_reduce_ops;
endmodule

(* techmap_simplemap *)
(* techmap_celltype = "$logic_not $logic_and $logic_or" *)
module simplemap_logic_ops;
endmodule

(* techmap_simplemap *)
(* techmap_celltype = "$slice $concat $mux" *)
module simplemap_various;
endmodule

(* techmap_simplemap *)
(* techmap_celltype = "$sr $dff $adff $dffsr $dlatch" *)
module simplemap_registers;
endmodule


// --------------------------------------------------------
// Trivial substitutions
// --------------------------------------------------------

module \$neg (A, Y);
	parameter A_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter Y_WIDTH = 1;

	input [A_WIDTH-1:0] A;
	output [Y_WIDTH-1:0] Y;

	\$sub #(
		.A_SIGNED(A_SIGNED),
		.B_SIGNED(A_SIGNED),
		.A_WIDTH(1),
		.B_WIDTH(A_WIDTH),
		.Y_WIDTH(Y_WIDTH)
	) _TECHMAP_REPLACE_ (
		.A(1'b0),
		.B(A),
		.Y(Y)
	);
endmodule

module \$ge (A, B, Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] Y;

	\$le #(
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

module \$gt (A, B, Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] Y;

	\$lt #(
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


// --------------------------------------------------------
// Shift operators
// --------------------------------------------------------

(* techmap_celltype = "$shr $shl $sshl $sshr" *)
module shift_ops_shr_shl_sshl_sshr (A, B, Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	parameter _TECHMAP_CELLTYPE_ = "";
	localparam shift_left = _TECHMAP_CELLTYPE_ == "$shl" || _TECHMAP_CELLTYPE_ == "$sshl";
	localparam sign_extend = A_SIGNED && _TECHMAP_CELLTYPE_ == "$sshr";

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] Y;

	localparam WIDTH = `MAX(A_WIDTH, Y_WIDTH);
	localparam BB_WIDTH = `MIN($clog2(shift_left ? Y_WIDTH : A_SIGNED ? WIDTH : A_WIDTH) + 1, B_WIDTH);

	wire [1023:0] _TECHMAP_DO_00_ = "proc;;";
	wire [1023:0] _TECHMAP_DO_01_ = "RECURSION; CONSTMAP; opt_muxtree; opt_const -mux_undef -mux_bool -fine;;;";

	integer i;
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
module shift_shiftx (A, B, Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] Y;

	localparam BB_WIDTH = `MIN($clog2(`MAX(A_WIDTH, Y_WIDTH)) + (B_SIGNED ? 2 : 1), B_WIDTH);
	localparam WIDTH = `MAX(A_WIDTH, Y_WIDTH) + (B_SIGNED ? 2**(BB_WIDTH-1) : 0);

	parameter _TECHMAP_CELLTYPE_ = "";
	localparam extbit = _TECHMAP_CELLTYPE_ == "$shift" ? 1'b0 : 1'bx;

	wire [1023:0] _TECHMAP_DO_00_ = "proc;;";
	wire [1023:0] _TECHMAP_DO_01_ = "CONSTMAP; opt_muxtree; opt_const -mux_undef -mux_bool -fine;;;";

	integer i;
	reg [WIDTH-1:0] buffer;
	reg overflow;

	always @* begin
		overflow = 0;
		buffer = {WIDTH{extbit}};
		buffer[`MAX(A_WIDTH, Y_WIDTH)-1:0] = A;

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

		for (i = BB_WIDTH-1; i >= 0; i = i-1)
			if (B[i]) begin
				if (B_SIGNED && i == BB_WIDTH-1)
					buffer = {buffer, {2**i{extbit}}};
				else if (2**i < WIDTH)
					buffer = {{2**i{extbit}}, buffer[WIDTH-1 : 2**i]};
				else
					buffer = {WIDTH{extbit}};
			end
	end

	assign Y = buffer;
endmodule


// --------------------------------------------------------
// ALU Infrastructure
// --------------------------------------------------------

module \$__alu_ripple (A, B, CI, Y, CO, CS);
	parameter WIDTH = 1;

	input [WIDTH-1:0] A, B;
	output [WIDTH-1:0] Y;

	input CI;
	output CO, CS;

	wire [WIDTH:0] carry;
	assign carry[0] = CI;
	assign CO = carry[WIDTH];
	assign CS = carry[WIDTH-1];

	genvar i;
	generate
		for (i = 0; i < WIDTH; i = i + 1)
		begin:V
			// {x, y} = a + b + c
			wire a, b, c, x, y;
			wire t1, t2, t3;

			\$_AND_ gate1 ( .A(a),  .B(b),  .Y(t1) );
			\$_XOR_ gate2 ( .A(a),  .B(b),  .Y(t2) );
			\$_AND_ gate3 ( .A(t2), .B(c),  .Y(t3) ); 
			\$_XOR_ gate4 ( .A(t2), .B(c),  .Y(y)  );
			\$_OR_  gate5 ( .A(t1), .B(t3), .Y(x)  );

			assign a = A[i], b = B[i], c = carry[i];
			assign carry[i+1] = x, Y[i] = y;
		end
	endgenerate
endmodule

module \$__lcu (P, G, CI, CO, PG, GG);
	parameter WIDTH = 1;

	input [WIDTH-1:0] P, G;
	input CI;

	output [WIDTH:0] CO;
	output PG, GG;

	assign CO[0] = CI;
	assign PG = 'bx, GG = 'bx;

	genvar i;
	generate
		// TBD: Actually implement a LCU topology
		for (i = 0; i < WIDTH; i = i + 1)
			assign CO[i+1] = G[i] | (P[i] & CO[i]);
	endgenerate
endmodule

module \$__alu_lookahead (A, B, CI, Y, CO, CS);
	parameter WIDTH = 1;

	input [WIDTH-1:0] A, B;
	output [WIDTH-1:0] Y;

	input CI;
	output CO, CS;

	wire [WIDTH-1:0] P, G;
	wire [WIDTH:0] C;

	assign CO = C[WIDTH];
	assign CS = C[WIDTH-1];

	genvar i;
	generate
		for (i = 0; i < WIDTH; i = i + 1)
		begin:V
			wire a, b, c, p, g, y;

			\$_AND_ gate1 ( .A(a),  .B(b),  .Y(g) );
			\$_XOR_ gate2 ( .A(a),  .B(b),  .Y(p) );
			\$_XOR_ gate3 ( .A(p),  .B(c),  .Y(y) );

			assign a = A[i], b = B[i], c = C[i];
			assign P[i] = p, G[i] = g, Y[i] = y;
		end
	endgenerate

	\$__lcu #(.WIDTH(WIDTH)) lcu (.P(P), .G(G), .CI(CI), .CO(C));
endmodule

module \$__alu (A, B, CI, S, Y, CO, CS);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] Y;

	// carry in, sub, carry out, carry sign
	input CI, S;
	output CO, CS;

	wire [Y_WIDTH-1:0] A_buf, B_buf;
	\$pos #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(Y_WIDTH)) A_conv (.A(A), .Y(A_buf));
	\$pos #(.A_SIGNED(B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(Y_WIDTH)) B_conv (.A(B), .Y(B_buf));

`ifdef ALU_RIPPLE
	\$__alu_ripple #(.WIDTH(Y_WIDTH)) _TECHMAP_REPLACE_ (.A(A_buf), .B(S ? ~B_buf : B_buf), .CI(CI), .Y(Y), .CO(CO), .CS(CS));
`else
	if (Y_WIDTH <= 4) begin
		\$__alu_ripple #(.WIDTH(Y_WIDTH)) _TECHMAP_REPLACE_ (.A(A_buf), .B(S ? ~B_buf : B_buf), .CI(CI), .Y(Y), .CO(CO), .CS(CS));
	end else begin
		\$__alu_lookahead #(.WIDTH(Y_WIDTH)) _TECHMAP_REPLACE_ (.A(A_buf), .B(S ? ~B_buf : B_buf), .CI(CI), .Y(Y), .CO(CO), .CS(CS));
	end
`endif
endmodule

`define ALU_COMMONS(_width, _ci, _s) """
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	localparam WIDTH = _width;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] Y;

	wire alu_co, alu_cs;
	wire [WIDTH-1:0] alu_y;

	\$__alu #(
		.A_SIGNED(A_SIGNED),
		.B_SIGNED(B_SIGNED),
		.A_WIDTH(A_WIDTH),
		.B_WIDTH(B_WIDTH),
		.Y_WIDTH(WIDTH)
	) alu (
		.A(A),
		.B(B),
		.CI(_ci),
		.S(_s),
		.Y(alu_y),
		.CO(alu_co),
		.CS(alu_cs)
	);

	wire cf, of, zf, sf;
	assign cf = !alu_co;
	assign of = alu_co ^ alu_cs;
	assign zf = ~|alu_y;
	assign sf = alu_y[WIDTH-1];
"""


// --------------------------------------------------------
// Compare cells
// --------------------------------------------------------

module \$lt (A, B, Y);
	wire [1023:0] _TECHMAP_DO_ = "RECURSION; CONSTMAP; opt_const -mux_undef -mux_bool -fine;;;";
	`ALU_COMMONS(`MAX(A_WIDTH, B_WIDTH), 1, 1)
	assign Y = A_SIGNED && B_SIGNED ? of != sf : cf;
endmodule

module \$le (A, B, Y);
	wire [1023:0] _TECHMAP_DO_ = "RECURSION; CONSTMAP; opt_const -mux_undef -mux_bool -fine;;;";
	`ALU_COMMONS(`MAX(A_WIDTH, B_WIDTH), 1, 1)
	assign Y = zf || (A_SIGNED && B_SIGNED ? of != sf : cf);
endmodule


// --------------------------------------------------------
// Add and Subtract
// --------------------------------------------------------

module \$add (A, B, Y);
	wire [1023:0] _TECHMAP_DO_ = "RECURSION; CONSTMAP; opt_const -mux_undef -mux_bool -fine;;;";
	`ALU_COMMONS(Y_WIDTH, 0, 0)
	assign Y = alu_y;
endmodule

module \$sub (A, B, Y);
	wire [1023:0] _TECHMAP_DO_ = "RECURSION; CONSTMAP; opt_const -mux_undef -mux_bool -fine;;;";
	`ALU_COMMONS(Y_WIDTH, 1, 1)
	assign Y = alu_y;
endmodule


// --------------------------------------------------------
// Multiply
// --------------------------------------------------------

module \$__arraymul (A, B, Y);
	parameter WIDTH = 8;
	input [WIDTH-1:0] A, B;
	output [WIDTH-1:0] Y;

	wire [WIDTH*WIDTH-1:0] partials;

	genvar i;
	assign partials[WIDTH-1 : 0] = A[0] ? B : 0;
	generate for (i = 1; i < WIDTH; i = i+1) begin:gen
		assign partials[WIDTH*(i+1)-1 : WIDTH*i] = (A[i] ? B << i : 0) + partials[WIDTH*i-1 : WIDTH*(i-1)];
	end endgenerate

	assign Y = partials[WIDTH*WIDTH-1 : WIDTH*(WIDTH-1)];
endmodule

module \$mul (A, B, Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] Y;

	wire [Y_WIDTH-1:0] A_buf, B_buf;
	\$pos #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(Y_WIDTH)) A_conv (.A(A), .Y(A_buf));
	\$pos #(.A_SIGNED(B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(Y_WIDTH)) B_conv (.A(B), .Y(B_buf));

	\$__arraymul #(
		.WIDTH(Y_WIDTH)
	) arraymul (
		.A(A_buf),
		.B(B_buf),
		.Y(Y)
	);
endmodule


// --------------------------------------------------------
// Divide and Modulo
// --------------------------------------------------------

module \$__div_mod_u (A, B, Y, R);
	parameter WIDTH = 1;

	input [WIDTH-1:0] A, B;
	output [WIDTH-1:0] Y, R;

	wire [WIDTH*WIDTH-1:0] chaindata;
	assign R = chaindata[WIDTH*WIDTH-1:WIDTH*(WIDTH-1)];

	genvar i;
	generate begin
		for (i = 0; i < WIDTH; i=i+1) begin:stage
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

module \$__div_mod (A, B, Y, R);
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

module \$div (A, B, Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] Y;

	\$__div_mod #(
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

module \$mod (A, B, Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] Y;

	\$__div_mod #(
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


// --------------------------------------------------------
// Power
// --------------------------------------------------------

module \$pow (A, B, Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] Y;

	wire _TECHMAP_FAIL_ = 1;
endmodule


// --------------------------------------------------------
// Equal and Not-Equal
// --------------------------------------------------------

module \$eq (A, B, Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	localparam WIDTH = A_WIDTH > B_WIDTH ? A_WIDTH : B_WIDTH;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] Y;

	wire carry, carry_sign;
	wire [WIDTH-1:0] A_buf, B_buf;
	\$bu0 #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(WIDTH)) A_conv (.A(A), .Y(A_buf));
	\$bu0 #(.A_SIGNED(B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(WIDTH)) B_conv (.A(B), .Y(B_buf));

	assign Y = ~|(A_buf ^ B_buf);
endmodule

module \$ne (A, B, Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	localparam WIDTH = A_WIDTH > B_WIDTH ? A_WIDTH : B_WIDTH;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] Y;

	wire carry, carry_sign;
	wire [WIDTH-1:0] A_buf, B_buf;
	\$bu0 #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(WIDTH)) A_conv (.A(A), .Y(A_buf));
	\$bu0 #(.A_SIGNED(B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(WIDTH)) B_conv (.A(B), .Y(B_buf));

	assign Y = |(A_buf ^ B_buf);
endmodule

module \$eqx (A, B, Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	localparam WIDTH = A_WIDTH > B_WIDTH ? A_WIDTH : B_WIDTH;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] Y;

	wire carry, carry_sign;
	wire [WIDTH-1:0] A_buf, B_buf;
	\$pos #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(WIDTH)) A_conv (.A(A), .Y(A_buf));
	\$pos #(.A_SIGNED(B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(WIDTH)) B_conv (.A(B), .Y(B_buf));

	assign Y = ~|(A_buf ^ B_buf);
endmodule

module \$nex (A, B, Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	localparam WIDTH = A_WIDTH > B_WIDTH ? A_WIDTH : B_WIDTH;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] Y;

	wire carry, carry_sign;
	wire [WIDTH-1:0] A_buf, B_buf;
	\$pos #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(WIDTH)) A_conv (.A(A), .Y(A_buf));
	\$pos #(.A_SIGNED(B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(WIDTH)) B_conv (.A(B), .Y(B_buf));

	assign Y = |(A_buf ^ B_buf);
endmodule


// --------------------------------------------------------
// Parallel Multiplexers
// --------------------------------------------------------

module \$pmux (A, B, S, Y);
	parameter WIDTH = 1;
	parameter S_WIDTH = 1;

	input [WIDTH-1:0] A;
	input [WIDTH*S_WIDTH-1:0] B;
	input [S_WIDTH-1:0] S;
	output [WIDTH-1:0] Y;

	wire [WIDTH-1:0] Y_B;

	genvar i, j;
	generate
		wire [WIDTH*S_WIDTH-1:0] B_AND_S;
		for (i = 0; i < S_WIDTH; i = i + 1) begin:B_AND
			assign B_AND_S[WIDTH*(i+1)-1:WIDTH*i] = B[WIDTH*(i+1)-1:WIDTH*i] & {WIDTH{S[i]}};
		end:B_AND
		for (i = 0; i < WIDTH; i = i + 1) begin:B_OR
			wire [S_WIDTH-1:0] B_AND_BITS;
			for (j = 0; j < S_WIDTH; j = j + 1) begin:B_AND_BITS_COLLECT
				assign B_AND_BITS[j] = B_AND_S[WIDTH*j+i];
			end:B_AND_BITS_COLLECT
			assign Y_B[i] = |B_AND_BITS;
		end:B_OR
	endgenerate

	assign Y = |S ? Y_B : A;
endmodule

module \$safe_pmux (A, B, S, Y);
	parameter WIDTH = 1;
	parameter S_WIDTH = 1;

	input [WIDTH-1:0] A;
	input [WIDTH*S_WIDTH-1:0] B;
	input [S_WIDTH-1:0] S;
	output [WIDTH-1:0] Y;

	wire [S_WIDTH-1:0] status_found_first;
	wire [S_WIDTH-1:0] status_found_second;

	genvar i;
	generate
		for (i = 0; i < S_WIDTH; i = i + 1) begin:GEN1
			wire pre_first;
			if (i > 0) begin:GEN2
				assign pre_first = status_found_first[i-1];
			end:GEN2 else begin:GEN3
				assign pre_first = 0;
			end:GEN3
			assign status_found_first[i] = pre_first | S[i];
			assign status_found_second[i] = pre_first & S[i];
		end:GEN1
	endgenerate

	\$pmux #(
		.WIDTH(WIDTH),
		.S_WIDTH(S_WIDTH)
	) pmux_cell (
		.A(A),
		.B(B),
		.S(S & {S_WIDTH{~|status_found_second}}),
		.Y(Y)
	);
endmodule

