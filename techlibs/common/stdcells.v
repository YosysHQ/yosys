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

// --------------------------------------------------------

(* techmap_simplemap *)
module \$not ;
endmodule

// --------------------------------------------------------

(* techmap_simplemap *)
module \$pos ;
endmodule

// --------------------------------------------------------

(* techmap_simplemap *)
module \$bu0 ;
endmodule

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
) sub (
	.A(1'b0),
	.B(A),
	.Y(Y)
);

endmodule

// --------------------------------------------------------

(* techmap_simplemap *)
module \$and ;
endmodule

// --------------------------------------------------------

(* techmap_simplemap *)
module \$or ;
endmodule

// --------------------------------------------------------

(* techmap_simplemap *)
module \$xor ;
endmodule

// --------------------------------------------------------

(* techmap_simplemap *)
module \$xnor ;
endmodule

// --------------------------------------------------------

(* techmap_simplemap *)
module \$reduce_and ;
endmodule

// --------------------------------------------------------

(* techmap_simplemap *)
module \$reduce_or ;
endmodule

// --------------------------------------------------------

(* techmap_simplemap *)
module \$reduce_xor ;
endmodule

// --------------------------------------------------------

(* techmap_simplemap *)
module \$reduce_xnor ;
endmodule

// --------------------------------------------------------

(* techmap_simplemap *)
module \$reduce_bool ;
endmodule

// --------------------------------------------------------

module \$__shift (XL, XR, A, Y);

parameter WIDTH = 1;
parameter SHIFT = 0;

input XL, XR;
input [WIDTH-1:0] A;
output [WIDTH-1:0] Y;

genvar i;
generate
	for (i = 0; i < WIDTH; i = i + 1) begin:V
		if (i+SHIFT < 0) begin
			assign Y[i] = XR;
		end else
		if (i+SHIFT < WIDTH) begin
			assign Y[i] = A[i+SHIFT];
		end else begin
			assign Y[i] = XL;
		end
	end
endgenerate

endmodule

// --------------------------------------------------------

module \$shl (A, B, Y);

parameter A_SIGNED = 0;
parameter B_SIGNED = 0;
parameter A_WIDTH = 1;
parameter B_WIDTH = 1;
parameter Y_WIDTH = 1;

parameter WIDTH = Y_WIDTH;
localparam BB_WIDTH = $clog2(WIDTH) + 2 < B_WIDTH ? $clog2(WIDTH) + 2 : B_WIDTH;

input [A_WIDTH-1:0] A;
input [B_WIDTH-1:0] B;
output [Y_WIDTH-1:0] Y;

genvar i;
generate
	wire [WIDTH*(BB_WIDTH+1)-1:0] chain;
	\$bu0 #(
		.A_SIGNED(A_SIGNED),
		.A_WIDTH(A_WIDTH),
		.Y_WIDTH(WIDTH)
	) expand (
		.A(A),
		.Y(chain[WIDTH-1:0])
	);
	assign Y = chain[WIDTH*(BB_WIDTH+1)-1 : WIDTH*BB_WIDTH];
	for (i = 0; i < BB_WIDTH; i = i + 1) begin:V
		wire [WIDTH-1:0] unshifted, shifted, result;
		assign unshifted = chain[WIDTH*i + WIDTH-1 : WIDTH*i];
		assign chain[WIDTH*(i+1) + WIDTH-1 : WIDTH*(i+1)] = result;
		wire BBIT;
		if (i == BB_WIDTH-1 && BB_WIDTH < B_WIDTH)
			assign BBIT = |B[B_WIDTH-1:BB_WIDTH-1];
		else
			assign BBIT = B[i];
		\$__shift #(
			.WIDTH(WIDTH),
			.SHIFT(0 - (2 ** (i > 30 ? 30 : i)))
		) sh (
			.XL(1'b0),
			.XR(1'b0),
			.A(unshifted),
			.Y(shifted)
		);
		\$mux #(
			.WIDTH(WIDTH)
		) mux (
			.A(unshifted),
			.B(shifted),
			.Y(result),
			.S(BBIT)
		);
	end
endgenerate

endmodule

// --------------------------------------------------------

module \$shr (A, B, Y);

parameter A_SIGNED = 0;
parameter B_SIGNED = 0;
parameter A_WIDTH = 1;
parameter B_WIDTH = 1;
parameter Y_WIDTH = 1;

localparam WIDTH = A_WIDTH > Y_WIDTH ? A_WIDTH : Y_WIDTH;
localparam BB_WIDTH = $clog2(WIDTH) + 2 < B_WIDTH ? $clog2(WIDTH) + 2 : B_WIDTH;

input [A_WIDTH-1:0] A;
input [B_WIDTH-1:0] B;
output [Y_WIDTH-1:0] Y;

genvar i;
generate
	wire [WIDTH*(BB_WIDTH+1)-1:0] chain;
	\$bu0 #(
		.A_SIGNED(A_SIGNED),
		.A_WIDTH(A_WIDTH),
		.Y_WIDTH(WIDTH)
	) expand (
		.A(A),
		.Y(chain[WIDTH-1:0])
	);
	assign Y = chain[WIDTH*(BB_WIDTH+1)-1 : WIDTH*BB_WIDTH];
	for (i = 0; i < BB_WIDTH; i = i + 1) begin:V
		wire [WIDTH-1:0] unshifted, shifted, result;
		assign unshifted = chain[WIDTH*i + WIDTH-1 : WIDTH*i];
		assign chain[WIDTH*(i+1) + WIDTH-1 : WIDTH*(i+1)] = result;
		wire BBIT;
		if (i == BB_WIDTH-1 && BB_WIDTH < B_WIDTH)
			assign BBIT = |B[B_WIDTH-1:BB_WIDTH-1];
		else
			assign BBIT = B[i];
		\$__shift #(
			.WIDTH(WIDTH),
			.SHIFT(2 ** (i > 30 ? 30 : i))
		) sh (
			.XL(1'b0),
			.XR(1'b0),
			.A(unshifted),
			.Y(shifted)
		);
		\$mux #(
			.WIDTH(WIDTH)
		) mux (
			.A(unshifted),
			.B(shifted),
			.Y(result),
			.S(BBIT)
		);
	end
endgenerate

endmodule

// --------------------------------------------------------

module \$sshl (A, B, Y);

parameter A_SIGNED = 0;
parameter B_SIGNED = 0;
parameter A_WIDTH = 1;
parameter B_WIDTH = 1;
parameter Y_WIDTH = 1;

localparam WIDTH = Y_WIDTH;
localparam BB_WIDTH = $clog2(WIDTH) + 2 < B_WIDTH ? $clog2(WIDTH) + 2 : B_WIDTH;

input [A_WIDTH-1:0] A;
input [B_WIDTH-1:0] B;
output [Y_WIDTH-1:0] Y;

genvar i;
generate
	wire [WIDTH*(BB_WIDTH+1)-1:0] chain;
	\$bu0 #(
		.A_SIGNED(A_SIGNED),
		.A_WIDTH(A_WIDTH),
		.Y_WIDTH(WIDTH)
	) expand (
		.A(A),
		.Y(chain[WIDTH-1:0])
	);
	assign Y = chain[WIDTH*(BB_WIDTH+1)-1 : WIDTH*BB_WIDTH];
	for (i = 0; i < BB_WIDTH; i = i + 1) begin:V
		wire [WIDTH-1:0] unshifted, shifted, result;
		assign unshifted = chain[WIDTH*i + WIDTH-1 : WIDTH*i];
		assign chain[WIDTH*(i+1) + WIDTH-1 : WIDTH*(i+1)] = result;
		wire BBIT;
		if (i == BB_WIDTH-1 && BB_WIDTH < B_WIDTH)
			assign BBIT = |B[B_WIDTH-1:BB_WIDTH-1];
		else
			assign BBIT = B[i];
		\$__shift #(
			.WIDTH(WIDTH),
			.SHIFT(0 - (2 ** (i > 30 ? 30 : i)))
		) sh (
			.XL(1'b0),
			.XR(1'b0),
			.A(unshifted),
			.Y(shifted)
		);
		\$mux #(
			.WIDTH(WIDTH)
		) mux (
			.A(unshifted),
			.B(shifted),
			.Y(result),
			.S(BBIT)
		);
	end
endgenerate

endmodule

// --------------------------------------------------------

module \$sshr (A, B, Y);

parameter A_SIGNED = 0;
parameter B_SIGNED = 0;
parameter A_WIDTH = 1;
parameter B_WIDTH = 1;
parameter Y_WIDTH = 1;

localparam WIDTH = A_WIDTH > Y_WIDTH ? A_WIDTH : Y_WIDTH;
localparam BB_WIDTH = $clog2(WIDTH) + 2 < B_WIDTH ? $clog2(WIDTH) + 2 : B_WIDTH;

input [A_WIDTH-1:0] A;
input [B_WIDTH-1:0] B;
output [Y_WIDTH-1:0] Y;

genvar i;
generate
	wire [WIDTH*(BB_WIDTH+1)-1:0] chain;
	\$bu0 #(
		.A_SIGNED(A_SIGNED),
		.A_WIDTH(A_WIDTH),
		.Y_WIDTH(WIDTH)
	) expand (
		.A(A),
		.Y(chain[WIDTH-1:0])
	);
	for (i = 0; i < Y_WIDTH; i = i + 1) begin:Y
		if (i < WIDTH) begin
			assign Y[i] = chain[WIDTH*BB_WIDTH + i];
		end else
		if (A_SIGNED) begin
			assign Y[i] = chain[WIDTH*BB_WIDTH + WIDTH-1];
		end else begin
			assign Y[i] = 0;
		end
	end
	for (i = 0; i < BB_WIDTH; i = i + 1) begin:V
		wire [WIDTH-1:0] unshifted, shifted, result;
		assign unshifted = chain[WIDTH*i + WIDTH-1 : WIDTH*i];
		assign chain[WIDTH*(i+1) + WIDTH-1 : WIDTH*(i+1)] = result;
		wire BBIT;
		if (i == BB_WIDTH-1 && BB_WIDTH < B_WIDTH)
			assign BBIT = |B[B_WIDTH-1:BB_WIDTH-1];
		else
			assign BBIT = B[i];
		\$__shift #(
			.WIDTH(WIDTH),
			.SHIFT(2 ** (i > 30 ? 30 : i))
		) sh (
			.XL(A_SIGNED && A[A_WIDTH-1]),
			.XR(1'b0),
			.A(unshifted),
			.Y(shifted)
		);
		\$mux #(
			.WIDTH(WIDTH)
		) mux (
			.A(unshifted),
			.B(shifted),
			.Y(result),
			.S(BBIT)
		);
	end
endgenerate

endmodule

// --------------------------------------------------------

module \$shift (A, B, Y);

parameter A_SIGNED = 0;
parameter B_SIGNED = 0;
parameter A_WIDTH = 1;
parameter B_WIDTH = 1;
parameter Y_WIDTH = 1;

input [A_WIDTH-1:0] A;
input [B_WIDTH-1:0] B;
output [Y_WIDTH-1:0] Y;

generate
	if (B_SIGNED) begin:BLOCK1
		assign Y = $signed(B) < 0 ? A << -B : A >> B;
	end else begin:BLOCK2
		assign Y = A >> B;
	end
endgenerate

endmodule

// --------------------------------------------------------

module \$shiftx (A, B, Y);

parameter A_SIGNED = 0;
parameter B_SIGNED = 0;
parameter A_WIDTH = 1;
parameter B_WIDTH = 1;
parameter Y_WIDTH = 1;

input [A_WIDTH-1:0] A;
input [B_WIDTH-1:0] B;
output [Y_WIDTH-1:0] Y;

\$shift #(
	.A_SIGNED(A_SIGNED),
	.B_SIGNED(B_SIGNED),
	.A_WIDTH(A_WIDTH),
	.B_WIDTH(B_WIDTH),
	.Y_WIDTH(Y_WIDTH),
) sh (
	.A(A),
	.B(B),
	.Y(Y)
);

endmodule

// --------------------------------------------------------

module \$__fulladd (A, B, C, X, Y);

// {X, Y} = A + B + C
input A, B, C;
output X, Y;

// {t1, t2} = A + B
wire t1, t2, t3;

\$_AND_ gate1 ( .A(A),  .B(B),  .Y(t1) );
\$_XOR_ gate2 ( .A(A),  .B(B),  .Y(t2) );
\$_AND_ gate3 ( .A(t2), .B(C),  .Y(t3) ); 
\$_XOR_ gate4 ( .A(t2), .B(C),  .Y(Y)  );
\$_OR_  gate5 ( .A(t1), .B(t3), .Y(X)  );

endmodule


// --------------------------------------------------------

module \$__alu (A, B, Cin, Y, Cout, Csign);

parameter WIDTH = 1;

input [WIDTH-1:0] A, B;
input Cin;

output [WIDTH-1:0] Y;
output Cout, Csign;

wire [WIDTH:0] carry;
assign carry[0] = Cin;
assign Cout = carry[WIDTH];
assign Csign = carry[WIDTH-1];

genvar i;
generate
	for (i = 0; i < WIDTH; i = i + 1) begin:V
		\$__fulladd adder (
			.A(A[i]),
			.B(B[i]),
			.C(carry[i]),
			.X(carry[i+1]),
			.Y(Y[i])
		);
	end
endgenerate

endmodule

// --------------------------------------------------------

module \$lt (A, B, Y);

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
wire [WIDTH-1:0] A_buf, B_buf, Y_buf;
\$pos #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(WIDTH)) A_conv (.A(A), .Y(A_buf));
\$pos #(.A_SIGNED(B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(WIDTH)) B_conv (.A(B), .Y(B_buf));

\$__alu #(
	.WIDTH(WIDTH)
) alu (
	.A(A_buf),
	.B(~B_buf),
	.Cin(1'b1),
	.Y(Y_buf),
	.Cout(carry),
	.Csign(carry_sign)
);

// ALU flags
wire cf, of, zf, sf;
assign cf = !carry;
assign of = carry ^ carry_sign;
assign zf = ~|Y_buf;
assign sf = Y_buf[WIDTH-1];

generate
	if (A_SIGNED && B_SIGNED) begin
		assign Y = of != sf;
	end else begin
		assign Y = cf;
	end
endgenerate

endmodule

// --------------------------------------------------------

module \$le (A, B, Y);

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
wire [WIDTH-1:0] A_buf, B_buf, Y_buf;
\$pos #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(WIDTH)) A_conv (.A(A), .Y(A_buf));
\$pos #(.A_SIGNED(B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(WIDTH)) B_conv (.A(B), .Y(B_buf));

\$__alu #(
	.WIDTH(WIDTH)
) alu (
	.A(A_buf),
	.B(~B_buf),
	.Cin(1'b1),
	.Y(Y_buf),
	.Cout(carry),
	.Csign(carry_sign)
);

// ALU flags
wire cf, of, zf, sf;
assign cf = !carry;
assign of = carry ^ carry_sign;
assign zf = ~|Y_buf;
assign sf = Y_buf[WIDTH-1];

generate
	if (A_SIGNED && B_SIGNED) begin
		assign Y = zf || (of != sf);
	end else begin
		assign Y = zf || cf;
	end
endgenerate

endmodule

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

// --------------------------------------------------------

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

// --------------------------------------------------------

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

// --------------------------------------------------------

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
) ge_via_le (
	.A(B),
	.B(A),
	.Y(Y)
);

endmodule

// --------------------------------------------------------

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
) gt_via_lt (
	.A(B),
	.B(A),
	.Y(Y)
);

endmodule

// --------------------------------------------------------

module \$add (A, B, Y);

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

\$__alu #(
	.WIDTH(Y_WIDTH)
) alu (
	.A(A_buf),
	.B(B_buf),
	.Cin(1'b0),
	.Y(Y)
);

endmodule

// --------------------------------------------------------

module \$sub (A, B, Y);

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

\$__alu #(
	.WIDTH(Y_WIDTH)
) alu (
	.A(A_buf),
	.B(~B_buf),
	.Cin(1'b1),
	.Y(Y)
);

endmodule

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

// --------------------------------------------------------

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

// --------------------------------------------------------

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

// --------------------------------------------------------

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

// --------------------------------------------------------

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

/****
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

wire signed [A_WIDTH:0] buffer_a = A_SIGNED ? $signed(A) : A;
wire signed [B_WIDTH:0] buffer_b = B_SIGNED ? $signed(B) : B;

assign Y = buffer_a ** buffer_b;

endmodule

// --------------------------------------------------------
****/

(* techmap_simplemap *)
module \$logic_not ;
endmodule

// --------------------------------------------------------

(* techmap_simplemap *)
module \$logic_and ;
endmodule

// --------------------------------------------------------

(* techmap_simplemap *)
module \$logic_or ;
endmodule

// --------------------------------------------------------

(* techmap_simplemap *)
module \$slice ;
endmodule

// --------------------------------------------------------

(* techmap_simplemap *)
module \$concat ;
endmodule

// --------------------------------------------------------

(* techmap_simplemap *)
module \$mux ;
endmodule

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

// --------------------------------------------------------

(* techmap_simplemap *)
module \$sr ;
endmodule

// --------------------------------------------------------

(* techmap_simplemap *)
module \$dff ;
endmodule

// --------------------------------------------------------

(* techmap_simplemap *)
module \$adff ;
endmodule

// --------------------------------------------------------

(* techmap_simplemap *)
module \$dffsr ;
endmodule

// --------------------------------------------------------

(* techmap_simplemap *)
module \$dlatch ;
endmodule

// --------------------------------------------------------

