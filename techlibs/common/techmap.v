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
(* techmap_celltype = "$pos $slice $concat $mux" *)
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

module \$__alu_ripple (A, B, CI, X, Y, CO);
	parameter WIDTH = 1;

	input [WIDTH-1:0] A, B;
	output [WIDTH-1:0] X, Y;

	input CI;
	output [WIDTH-1:0] CO;

	wire [WIDTH:0] carry;
	assign carry[0] = CI;
	assign CO = carry[WIDTH:1];

	genvar i;
	generate
		for (i = 0; i < WIDTH; i = i+1)
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
			assign carry[i+1] = x, X[i] = t2, Y[i] = y;
		end
	endgenerate
endmodule

module \$__lcu (P, G, CI, CO);
	parameter WIDTH = 2;

	input [WIDTH-1:0] P, G;
	input CI;

	output [WIDTH-1:0] CO;

	integer i, j;
	reg [WIDTH-1:0] p, g;

	wire [1023:0] _TECHMAP_DO_ = "proc; opt -fast";

	always @* begin
		p = P;
		g = G;

		// in almost all cases CI will be constant zero
		g[0] = g[0] | (p[0] & CI);

		// [[CITE]] Brent Kung Adder
		// R. P. Brent and H. T. Kung, “A Regular Layout for Parallel Adders”,
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

module \$__alu_lookahead (A, B, CI, X, Y, CO);
	parameter WIDTH = 1;

	input [WIDTH-1:0] A, B;
	output [WIDTH-1:0] X, Y;

	input CI;
	output [WIDTH-1:0] CO;

	wire [WIDTH-1:0] P, G;
	wire [WIDTH:0] carry;

	genvar i;
	generate
		for (i = 0; i < WIDTH; i = i+1)
		begin:V
			wire a, b, c, p, g, y;

			\$_AND_ gate1 ( .A(a),  .B(b),  .Y(g) );
			\$_XOR_ gate2 ( .A(a),  .B(b),  .Y(p) );
			\$_XOR_ gate3 ( .A(p),  .B(c),  .Y(y) );

			assign a = A[i], b = B[i], c = carry[i];
			assign P[i] = p, G[i] = g, X[i] = p, Y[i] = y;
		end
	endgenerate

	\$__lcu #(.WIDTH(WIDTH)) lcu (.P(P), .G(G), .CI(CI), .CO(CO));
	assign carry = {CO, CI};
endmodule

module \$alu (A, B, CI, BI, X, Y, CO);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] X, Y;

	input CI, BI;
	output [Y_WIDTH-1:0] CO;

	wire [Y_WIDTH-1:0] A_buf, B_buf;
	\$pos #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(Y_WIDTH)) A_conv (.A(A), .Y(A_buf));
	\$pos #(.A_SIGNED(B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(Y_WIDTH)) B_conv (.A(B), .Y(B_buf));

`ifdef ALU_RIPPLE
	\$__alu_ripple #(.WIDTH(Y_WIDTH)) _TECHMAP_REPLACE_ (.A(A_buf), .B(BI ? ~B_buf : B_buf), .CI(CI), .X(X), .Y(Y), .CO(CO));
`else
	if (Y_WIDTH <= 4) begin
		\$__alu_ripple #(.WIDTH(Y_WIDTH)) _TECHMAP_REPLACE_ (.A(A_buf), .B(BI ? ~B_buf : B_buf), .CI(CI), .X(X), .Y(Y), .CO(CO));
	end else begin
		\$__alu_lookahead #(.WIDTH(Y_WIDTH)) _TECHMAP_REPLACE_ (.A(A_buf), .B(BI ? ~B_buf : B_buf), .CI(CI), .X(X), .Y(Y), .CO(CO));
	end
`endif
endmodule


// --------------------------------------------------------
// ALU Cell Types: Compare, Add, Subtract
// --------------------------------------------------------

`define ALU_COMMONS(_width, _sub) """
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	localparam WIDTH = _width;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] Y;

	wire [WIDTH-1:0] alu_x, alu_y, alu_co;
	wire [WIDTH:0] carry = {alu_co, |_sub};

	\$alu #(
		.A_SIGNED(A_SIGNED),
		.B_SIGNED(B_SIGNED),
		.A_WIDTH(A_WIDTH),
		.B_WIDTH(B_WIDTH),
		.Y_WIDTH(WIDTH)
	) alu (
		.A(A),
		.B(B),
		.CI(|_sub),
		.BI(|_sub),
		.X(alu_x),
		.Y(alu_y),
		.CO(alu_co)
	);

	wire cf, of, zf, sf;
	assign cf = !carry[WIDTH];
	assign of = carry[WIDTH] ^ carry[WIDTH-1];
	assign sf = alu_y[WIDTH-1];
"""

module \$lt (A, B, Y);
	wire [1023:0] _TECHMAP_DO_ = "RECURSION; opt_const -mux_undef -mux_bool -fine;;;";
	`ALU_COMMONS(`MAX(A_WIDTH, B_WIDTH), 1)
	assign Y = A_SIGNED && B_SIGNED ? of != sf : cf;
endmodule

module \$le (A, B, Y);
	wire [1023:0] _TECHMAP_DO_ = "RECURSION; opt_const -mux_undef -mux_bool -fine;;;";
	`ALU_COMMONS(`MAX(A_WIDTH, B_WIDTH), 1)
	assign Y = &alu_x || (A_SIGNED && B_SIGNED ? of != sf : cf);
endmodule

module \$add (A, B, Y);
	wire [1023:0] _TECHMAP_DO_ = "RECURSION; opt_const -mux_undef -mux_bool -fine;;;";
	`ALU_COMMONS(Y_WIDTH, 0)
	assign Y = alu_y;
endmodule

module \$sub (A, B, Y);
	wire [1023:0] _TECHMAP_DO_ = "RECURSION; opt_const -mux_undef -mux_bool -fine;;;";
	`ALU_COMMONS(Y_WIDTH, 1)
	assign Y = alu_y;
endmodule


// --------------------------------------------------------
// Multiply
// --------------------------------------------------------

module \$__acc_set (acc_new, value);
	parameter WIDTH = 1;
	output reg [2*WIDTH-1:0] acc_new;
	input [WIDTH-1:0] value;

	wire [1023:0] _TECHMAP_DO_ = "proc;;;";

	integer k;
	always @* begin
		for (k = 0; k < WIDTH; k = k+1) begin
			acc_new[2*k +: 2] = value[k];
		end
	end
endmodule

module \$__acc_add (acc_new, acc_old, value);
	parameter WIDTH = 1;
	output reg [2*WIDTH-1:0] acc_new;
	input [2*WIDTH-1:0] acc_old;
	input [WIDTH-1:0] value;

	wire [1023:0] _TECHMAP_DO_ = "proc; simplemap; opt -purge";

	integer k;
	reg a, b, c;

	always @* begin
		for (k = 0; k < WIDTH; k = k+1) begin
			a = acc_old[2*k];
			b = k ? acc_old[2*k-1] : 1'b0;
			c = value[k];
			acc_new[2*k] = (a ^ b) ^ c;
			acc_new[2*k+1] = (a & b) | ((a ^ b) & c);
		end
	end
endmodule

module \$__acc_get (value, acc);
	parameter WIDTH = 1;
	output reg [WIDTH-1:0] value;
	input [2*WIDTH-1:0] acc;

	wire [1023:0] _TECHMAP_DO_ = "proc;;;";

	integer k;

	always @* begin
		// at the end of the multiplier chain the carry-save accumulator
		// should also have propagated all carries. thus we just need to
		// copy the even bits from the carry accumulator to the output.
		for (k = 0; k < WIDTH; k = k+1) begin
			value[k] = acc[2*k];
		end
	end
endmodule

module \$__acc_mul (A, B, Y);
	parameter WIDTH = 1;
	input [WIDTH-1:0] A, B;
	output [WIDTH-1:0] Y;

	wire [1023:0] _TECHMAP_DO_ = "proc;;";

	integer i;
	reg [WIDTH-1:0] x;
	reg [2*WIDTH-1:0] y;

	(* via_celltype = "\\$__acc_set acc_new" *)
	(* via_celltype_defparam_WIDTH = WIDTH *)
	function [2*WIDTH-1:0] acc_set;
		input [WIDTH-1:0] value;
	endfunction

	(* via_celltype = "\\$__acc_add acc_new" *)
	(* via_celltype_defparam_WIDTH = WIDTH *)
	function [2*WIDTH-1:0] acc_add;
		input [2*WIDTH-1:0] acc_old;
		input [WIDTH-1:0] value;
	endfunction

	(* via_celltype = "\\$__acc_get value" *)
	(* via_celltype_defparam_WIDTH = WIDTH *)
	function [WIDTH-1:0] acc_get;
		input [2*WIDTH-1:0] acc;
	endfunction

	always @* begin
		x = B;
		y = acc_set(A[0] ? x : 1'b0);
		for (i = 1; i < WIDTH; i = i+1) begin
			x = {x[WIDTH-2:0], 1'b0};
			y = acc_add(y, A[i] ? x : 1'b0);
		end
	end

	assign Y = acc_get(y);
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

	wire [1023:0] _TECHMAP_DO_ = "RECURSION; CONSTMAP; opt -purge";

	wire [Y_WIDTH-1:0] A_buf, B_buf;
	\$pos #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(Y_WIDTH)) A_conv (.A(A), .Y(A_buf));
	\$pos #(.A_SIGNED(B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(Y_WIDTH)) B_conv (.A(B), .Y(B_buf));

	\$__acc_mul #(
		.WIDTH(Y_WIDTH)
	) _TECHMAP_REPLACE_ (
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
	\$pos #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(WIDTH)) A_conv (.A(A), .Y(A_buf));
	\$pos #(.A_SIGNED(B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(WIDTH)) B_conv (.A(B), .Y(B_buf));

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
	\$pos #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(WIDTH)) A_conv (.A(A), .Y(A_buf));
	\$pos #(.A_SIGNED(B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(WIDTH)) B_conv (.A(B), .Y(B_buf));

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


// --------------------------------------------------------
// LUTs
// --------------------------------------------------------

`ifndef NOLUT
module \$lut (A, Y);
	parameter WIDTH = 1;
	parameter LUT = 0;

	input [WIDTH-1:0] A;
	output Y;

	assign Y = LUT[A];
endmodule
`endif

