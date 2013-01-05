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

module \$not (A, Y);

parameter A_SIGNED = 0;
parameter A_WIDTH = 1;
parameter Y_WIDTH = 1;

input [A_WIDTH-1:0] A;
output [Y_WIDTH-1:0] Y;

genvar i;
generate
	for (i = 0; i < Y_WIDTH; i = i + 1) begin:V
		if (i < A_WIDTH) begin
			 \$_INV_ gate (
				.A(A[i]),
				.Y(Y[i])
			);
		end else begin
			assign Y[i] = 0;
		end
	end
endgenerate

endmodule

// --------------------------------------------------------

module \$pos (A, Y);

parameter A_SIGNED = 0;
parameter A_WIDTH = 1;
parameter Y_WIDTH = 1;

input [A_WIDTH-1:0] A;
output [Y_WIDTH-1:0] Y;

genvar i;
generate
	for (i = 0; i < Y_WIDTH; i = i + 1) begin:V
		if (i < A_WIDTH) begin
			assign Y[i] = A[i];
		end else if (A_SIGNED) begin
			assign Y[i] = A[A_WIDTH-1];
		end else begin
			assign Y[i] = 0;
		end
	end
endgenerate

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
	.A(0),
	.B(A),
	.Y(Y)
);

endmodule

// --------------------------------------------------------

module \$and (A, B, Y);

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

genvar i;
generate
	for (i = 0; i < Y_WIDTH; i = i + 1) begin:V
		 \$_AND_ gate (
			.A(A_buf[i]),
			.B(B_buf[i]),
			.Y(Y[i])
		);
	end
endgenerate

endmodule

// --------------------------------------------------------

module \$or (A, B, Y);

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

genvar i;
generate
	for (i = 0; i < Y_WIDTH; i = i + 1) begin:V
		 \$_OR_ gate (
			.A(A_buf[i]),
			.B(B_buf[i]),
			.Y(Y[i])
		);
	end
endgenerate

endmodule

// --------------------------------------------------------

module \$xor (A, B, Y);

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

genvar i;
generate
	for (i = 0; i < Y_WIDTH; i = i + 1) begin:V
		 \$_XOR_ gate (
			.A(A_buf[i]),
			.B(B_buf[i]),
			.Y(Y[i])
		);
	end
endgenerate

endmodule

// --------------------------------------------------------

module \$xnor (A, B, Y);

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

genvar i;
generate
	for (i = 0; i < Y_WIDTH; i = i + 1) begin:V
		wire tmp;
		 \$_XOR_ gate1 (
			.A(A_buf[i]),
			.B(B_buf[i]),
			.Y(tmp)
		);
		 \$_INV_ gate2 (
			.A(tmp),
			.Y(Y[i])
		);
	end
endgenerate

endmodule

// --------------------------------------------------------

module \$reduce_and (A, Y);

parameter A_SIGNED = 0;
parameter A_WIDTH = 1;
parameter Y_WIDTH = 1;

input [A_WIDTH-1:0] A;
output Y;

wire [A_WIDTH-1:0] buffer;

genvar i;
generate
	for (i = 1; i < A_WIDTH; i = i + 1) begin:V
		 \$_AND_ gate (
			.A(A[i]),
			.B(buffer[i-1]),
			.Y(buffer[i])
		);
	end
endgenerate

assign buffer[0] = A[0];
assign Y = buffer[A_WIDTH-1];

endmodule

// --------------------------------------------------------

module \$reduce_or (A, Y);

parameter A_SIGNED = 0;
parameter A_WIDTH = 1;
parameter Y_WIDTH = 1;

input [A_WIDTH-1:0] A;
output Y;

wire [A_WIDTH-1:0] buffer;

genvar i;
generate
	for (i = 1; i < A_WIDTH; i = i + 1) begin:V
		 \$_OR_ gate (
			.A(A[i]),
			.B(buffer[i-1]),
			.Y(buffer[i])
		);
	end
endgenerate

assign buffer[0] = A[0];
assign Y = buffer[A_WIDTH-1];

endmodule

// --------------------------------------------------------

module \$reduce_xor (A, Y);

parameter A_SIGNED = 0;
parameter A_WIDTH = 1;
parameter Y_WIDTH = 1;

input [A_WIDTH-1:0] A;
output Y;

wire [A_WIDTH-1:0] buffer;

genvar i;
generate
	for (i = 1; i < A_WIDTH; i = i + 1) begin:V
		 \$_XOR_ gate (
			.A(A[i]),
			.B(buffer[i-1]),
			.Y(buffer[i])
		);
	end
endgenerate

assign buffer[0] = A[0];
assign Y = buffer[A_WIDTH-1];

endmodule


// --------------------------------------------------------

module \$reduce_xnor (A, Y);

parameter A_SIGNED = 0;
parameter A_WIDTH = 1;
parameter Y_WIDTH = 1;

input [A_WIDTH-1:0] A;
output Y;

wire [A_WIDTH-1:0] buffer;

genvar i;
generate
	for (i = 1; i < A_WIDTH; i = i + 1) begin:V
		 \$_XOR_ gate (
			.A(A[i]),
			.B(buffer[i-1]),
			.Y(buffer[i])
		);
	end
endgenerate

assign buffer[0] = A[0];
 \$_INV_ gate_inv (
	.A(buffer[A_WIDTH-1]),
	.Y(Y)
);

endmodule

// --------------------------------------------------------

module \$reduce_bool (A, Y);

parameter A_SIGNED = 0;
parameter A_WIDTH = 1;
parameter Y_WIDTH = 1;

input [A_WIDTH-1:0] A;
output Y;

wire [A_WIDTH-1:0] buffer;

genvar i;
generate
	for (i = 1; i < A_WIDTH; i = i + 1) begin:V
		 \$_OR_ gate (
			.A(A[i]),
			.B(buffer[i-1]),
			.Y(buffer[i])
		);
	end
endgenerate

assign buffer[0] = A[0];
assign Y = buffer[A_WIDTH-1];

endmodule

// --------------------------------------------------------

module \$shift (X, A, Y);

parameter WIDTH = 1;
parameter SHIFT = 0;

input X;
input [WIDTH-1:0] A;
output [WIDTH-1:0] Y;

genvar i;
generate
	for (i = 0; i < WIDTH; i = i + 1) begin:V
		if (i+SHIFT < 0) begin
			assign Y[i] = 0;
		end else
		if (i+SHIFT < WIDTH) begin
			assign Y[i] = A[i+SHIFT];
		end else begin
			assign Y[i] = X;
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

input [A_WIDTH-1:0] A;
input [B_WIDTH-1:0] B;
output [Y_WIDTH-1:0] Y;

genvar i;
generate
	wire [WIDTH*(B_WIDTH+1)-1:0] chain;
	\$pos #(
		.A_SIGNED(A_SIGNED),
		.A_WIDTH(A_WIDTH),
		.Y_WIDTH(WIDTH)
	) expand (
		.A(A),
		.Y(chain[WIDTH-1:0])
	);
	assign Y = chain[WIDTH*(B_WIDTH+1)-1 : WIDTH*B_WIDTH];
	for (i = 0; i < B_WIDTH; i = i + 1) begin:V
		wire [WIDTH-1:0] unshifted, shifted, result;
		assign unshifted = chain[WIDTH*i + WIDTH-1 : WIDTH*i];
		assign chain[WIDTH*(i+1) + WIDTH-1 : WIDTH*(i+1)] = result;
		\$shift #(
			.WIDTH(WIDTH),
			.SHIFT(0 - (2 ** i))
		) sh (
			.X(0),
			.A(unshifted),
			.Y(shifted)
		);
		\$mux #(
			.WIDTH(WIDTH)
		) mux (
			.A(unshifted),
			.B(shifted),
			.Y(result),
			.S(B[i])
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

parameter WIDTH = A_WIDTH > Y_WIDTH ? A_WIDTH : Y_WIDTH;

input [A_WIDTH-1:0] A;
input [B_WIDTH-1:0] B;
output [Y_WIDTH-1:0] Y;

genvar i;
generate
	wire [WIDTH*(B_WIDTH+1)-1:0] chain;
	\$pos #(
		.A_SIGNED(A_SIGNED),
		.A_WIDTH(A_WIDTH),
		.Y_WIDTH(WIDTH)
	) expand (
		.A(A),
		.Y(chain[WIDTH-1:0])
	);
	assign Y = chain[WIDTH*(B_WIDTH+1)-1 : WIDTH*B_WIDTH];
	for (i = 0; i < B_WIDTH; i = i + 1) begin:V
		wire [WIDTH-1:0] unshifted, shifted, result;
		assign unshifted = chain[WIDTH*i + WIDTH-1 : WIDTH*i];
		assign chain[WIDTH*(i+1) + WIDTH-1 : WIDTH*(i+1)] = result;
		\$shift #(
			.WIDTH(WIDTH),
			.SHIFT(2 ** i)
		) sh (
			.X(0),
			.A(unshifted),
			.Y(shifted)
		);
		\$mux #(
			.WIDTH(WIDTH)
		) mux (
			.A(unshifted),
			.B(shifted),
			.Y(result),
			.S(B[i])
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

parameter WIDTH = Y_WIDTH;

input [A_WIDTH-1:0] A;
input [B_WIDTH-1:0] B;
output [Y_WIDTH-1:0] Y;

genvar i;
generate
	wire [WIDTH*(B_WIDTH+1)-1:0] chain;
	\$pos #(
		.A_SIGNED(A_SIGNED),
		.A_WIDTH(A_WIDTH),
		.Y_WIDTH(WIDTH)
	) expand (
		.A(A),
		.Y(chain[WIDTH-1:0])
	);
	assign Y = chain[WIDTH*(B_WIDTH+1)-1 : WIDTH*B_WIDTH];
	for (i = 0; i < B_WIDTH; i = i + 1) begin:V
		wire [WIDTH-1:0] unshifted, shifted, result;
		assign unshifted = chain[WIDTH*i + WIDTH-1 : WIDTH*i];
		assign chain[WIDTH*(i+1) + WIDTH-1 : WIDTH*(i+1)] = result;
		\$shift #(
			.WIDTH(WIDTH),
			.SHIFT(0 - (2 ** i))
		) sh (
			.X(0),
			.A(unshifted),
			.Y(shifted)
		);
		\$mux #(
			.WIDTH(WIDTH)
		) mux (
			.A(unshifted),
			.B(shifted),
			.Y(result),
			.S(B[i])
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

parameter WIDTH = A_WIDTH > Y_WIDTH ? A_WIDTH : Y_WIDTH;

input [A_WIDTH-1:0] A;
input [B_WIDTH-1:0] B;
output [Y_WIDTH-1:0] Y;

genvar i;
generate
	wire [WIDTH*(B_WIDTH+1)-1:0] chain;
	\$pos #(
		.A_SIGNED(A_SIGNED),
		.A_WIDTH(A_WIDTH),
		.Y_WIDTH(WIDTH)
	) expand (
		.A(A),
		.Y(chain[WIDTH-1:0])
	);
	for (i = 0; i < Y_WIDTH; i = i + 1) begin:Y
		if (i < WIDTH) begin
			assign Y[i] = chain[WIDTH*B_WIDTH + i];
		end else
		if (A_SIGNED) begin
			assign Y[i] = chain[WIDTH*B_WIDTH + WIDTH-1];
		end else begin
			assign Y[i] = 0;
		end
	end
	for (i = 0; i < B_WIDTH; i = i + 1) begin:V
		wire [WIDTH-1:0] unshifted, shifted, result;
		assign unshifted = chain[WIDTH*i + WIDTH-1 : WIDTH*i];
		assign chain[WIDTH*(i+1) + WIDTH-1 : WIDTH*(i+1)] = result;
		\$shift #(
			.WIDTH(WIDTH),
			.SHIFT(2 ** i)
		) sh (
			.X(A_SIGNED && A[A_WIDTH-1]),
			.A(unshifted),
			.Y(shifted)
		);
		\$mux #(
			.WIDTH(WIDTH)
		) mux (
			.A(unshifted),
			.B(shifted),
			.Y(result),
			.S(B[i])
		);
	end
endgenerate

endmodule

// --------------------------------------------------------

module \$fulladd (A, B, C, X, Y);

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

module \$alu (A, B, Cin, Y, Cout, Csign);

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
		\$fulladd adder (
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

parameter WIDTH = A_WIDTH > B_WIDTH ? A_WIDTH : B_WIDTH;

input [A_WIDTH-1:0] A;
input [B_WIDTH-1:0] B;
output Y;

wire carry, carry_sign;
wire [WIDTH-1:0] A_buf, B_buf, Y_buf;
\$pos #(.A_SIGNED(A_SIGNED && B_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(WIDTH)) A_conv (.A(A), .Y(A_buf));
\$pos #(.A_SIGNED(A_SIGNED && B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(WIDTH)) B_conv (.A(B), .Y(B_buf));

\$alu #(
	.WIDTH(WIDTH)
) alu (
	.A(A_buf),
	.B(~B_buf),
	.Cin(1'b1),
	.Y(Y_buf),
	.Cout(carry),
	.Csign(carry_sign),
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

parameter WIDTH = A_WIDTH > B_WIDTH ? A_WIDTH : B_WIDTH;

input [A_WIDTH-1:0] A;
input [B_WIDTH-1:0] B;
output Y;

wire carry, carry_sign;
wire [WIDTH-1:0] A_buf, B_buf, Y_buf;
\$pos #(.A_SIGNED(A_SIGNED && B_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(WIDTH)) A_conv (.A(A), .Y(A_buf));
\$pos #(.A_SIGNED(A_SIGNED && B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(WIDTH)) B_conv (.A(B), .Y(B_buf));

\$alu #(
	.WIDTH(WIDTH)
) alu (
	.A(A_buf),
	.B(~B_buf),
	.Cin(1'b1),
	.Y(Y_buf),
	.Cout(carry),
	.Csign(carry_sign),
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

parameter WIDTH = A_WIDTH > B_WIDTH ? A_WIDTH : B_WIDTH;

input [A_WIDTH-1:0] A;
input [B_WIDTH-1:0] B;
output Y;

wire carry, carry_sign;
wire [WIDTH-1:0] A_buf, B_buf, Y_buf;
\$pos #(.A_SIGNED(A_SIGNED && B_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(WIDTH)) A_conv (.A(A), .Y(A_buf));
\$pos #(.A_SIGNED(A_SIGNED && B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(WIDTH)) B_conv (.A(B), .Y(B_buf));

assign Y = ~|(A_buf ^ B_buf);

endmodule

// --------------------------------------------------------

module \$ne (A, B, Y);

parameter A_SIGNED = 0;
parameter B_SIGNED = 0;
parameter A_WIDTH = 1;
parameter B_WIDTH = 1;
parameter Y_WIDTH = 1;

parameter WIDTH = A_WIDTH > B_WIDTH ? A_WIDTH : B_WIDTH;

input [A_WIDTH-1:0] A;
input [B_WIDTH-1:0] B;
output Y;

wire carry, carry_sign;
wire [WIDTH-1:0] A_buf, B_buf, Y_buf;
\$pos #(.A_SIGNED(A_SIGNED && B_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(WIDTH)) A_conv (.A(A), .Y(A_buf));
\$pos #(.A_SIGNED(A_SIGNED && B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(WIDTH)) B_conv (.A(B), .Y(B_buf));

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
output Y;

\$le #(
	.A_SIGNED(B_SIGNED),
	.B_SIGNED(A_SIGNED),
	.A_WIDTH(B_WIDTH),
	.B_WIDTH(A_WIDTH)
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
output Y;

\$lt #(
	.A_SIGNED(B_SIGNED),
	.B_SIGNED(A_SIGNED),
	.A_WIDTH(B_WIDTH),
	.B_WIDTH(A_WIDTH)
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
\$pos #(.A_SIGNED(A_SIGNED && B_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(Y_WIDTH)) A_conv (.A(A), .Y(A_buf));
\$pos #(.A_SIGNED(A_SIGNED && B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(Y_WIDTH)) B_conv (.A(B), .Y(B_buf));

\$alu #(
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
\$pos #(.A_SIGNED(A_SIGNED && B_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(Y_WIDTH)) A_conv (.A(A), .Y(A_buf));
\$pos #(.A_SIGNED(A_SIGNED && B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(Y_WIDTH)) B_conv (.A(B), .Y(B_buf));

\$alu #(
	.WIDTH(Y_WIDTH)
) alu (
	.A(A_buf),
	.B(~B_buf),
	.Cin(1'b1),
	.Y(Y)
);

endmodule

/****
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

wire signed [A_WIDTH:0] buffer_a = A_SIGNED ? $signed(A) : A;
wire signed [B_WIDTH:0] buffer_b = B_SIGNED ? $signed(B) : B;

assign Y = buffer_a * buffer_b;

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

wire signed [A_WIDTH:0] buffer_a = A_SIGNED ? $signed(A) : A;
wire signed [B_WIDTH:0] buffer_b = B_SIGNED ? $signed(B) : B;

assign Y = buffer_a / buffer_b;

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

wire signed [A_WIDTH:0] buffer_a = A_SIGNED ? $signed(A) : A;
wire signed [B_WIDTH:0] buffer_b = B_SIGNED ? $signed(B) : B;

assign Y = buffer_a % buffer_b;

endmodule

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

module \$logic_not (A, Y);

parameter A_SIGNED = 0;
parameter A_WIDTH = 1;
parameter Y_WIDTH = 1;

input [A_WIDTH-1:0] A;
output [Y_WIDTH-1:0] Y;

wire A_buf;

\$reduce_bool #(
	.A_SIGNED(A_SIGNED),
	.A_WIDTH(A_WIDTH)
) A_logic (
	.A(A), 
	.Y(A_buf)
);

 \$_INV_ gate (
	.A(A_buf),
	.Y(Y[0])
);

generate
	if (Y_WIDTH > 1) begin:V
		assign Y[Y_WIDTH-1:1] = 0;
	end
endgenerate

endmodule

// --------------------------------------------------------

module \$logic_and (A, B, Y);

parameter A_SIGNED = 0;
parameter B_SIGNED = 0;
parameter A_WIDTH = 1;
parameter B_WIDTH = 1;
parameter Y_WIDTH = 1;

input [A_WIDTH-1:0] A;
input [B_WIDTH-1:0] B;
output [Y_WIDTH-1:0] Y;

wire A_buf, B_buf;

\$reduce_bool #(
	.A_SIGNED(A_SIGNED),
	.A_WIDTH(A_WIDTH)
) A_logic (
	.A(A), 
	.Y(A_buf)
);

\$reduce_bool #(
	.A_SIGNED(B_SIGNED),
	.A_WIDTH(B_WIDTH)
) B_logic (
	.A(B), 
	.Y(B_buf)
);

 \$_AND_ gate (
	.A(A_buf),
	.B(B_buf),
	.Y(Y[0])
);

generate
	if (Y_WIDTH > 1) begin:V
		assign Y[Y_WIDTH-1:1] = 0;
	end
endgenerate

endmodule

// --------------------------------------------------------

module \$logic_or (A, B, Y);

parameter A_SIGNED = 0;
parameter B_SIGNED = 0;
parameter A_WIDTH = 1;
parameter B_WIDTH = 1;
parameter Y_WIDTH = 1;

input [A_WIDTH-1:0] A;
input [B_WIDTH-1:0] B;
output [Y_WIDTH-1:0] Y;

wire A_buf, B_buf;

\$reduce_bool #(
	.A_SIGNED(A_SIGNED),
	.A_WIDTH(A_WIDTH)
) A_logic (
	.A(A), 
	.Y(A_buf)
);

\$reduce_bool #(
	.A_SIGNED(B_SIGNED),
	.A_WIDTH(B_WIDTH)
) B_logic (
	.A(B), 
	.Y(B_buf)
);

 \$_OR_ gate (
	.A(A_buf),
	.B(B_buf),
	.Y(Y[0])
);

generate
	if (Y_WIDTH > 1) begin:V
		assign Y[Y_WIDTH-1:1] = 0;
	end
endgenerate

endmodule

// --------------------------------------------------------

module \$mux (A, B, S, Y);

parameter WIDTH = 1;

input [WIDTH-1:0] A, B;
input S;
output [WIDTH-1:0] Y;

genvar i;
generate
	for (i = 0; i < WIDTH; i = i + 1) begin:V
		\$_MUX_ gate (
			.A(A[i]),
			.B(B[i]),
			.S(S),
			.Y(Y[i])
		);
	end
endgenerate

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

module \$dff (CLK, D, Q);

parameter WIDTH = 1;
parameter CLK_POLARITY = 1'b1;

input CLK;
input [WIDTH-1:0] D;
output [WIDTH-1:0] Q;

genvar i;
generate
	if (CLK_POLARITY == 0)
		for (i = 0; i < WIDTH; i = i + 1) begin:V
			 \$_DFF_N_ ff (
				.D(D[i]),
				.Q(Q[i]),
				.C(CLK)
			);
		end
	if (CLK_POLARITY != 0)
		for (i = 0; i < WIDTH; i = i + 1) begin:V
			 \$_DFF_P_ ff (
				.D(D[i]),
				.Q(Q[i]),
				.C(CLK)
			);
		end
endgenerate

endmodule

// --------------------------------------------------------

module \$adff (CLK, ARST, D, Q);

parameter WIDTH = 1;
parameter CLK_POLARITY = 1'b1;
parameter ARST_POLARITY = 1'b1;
parameter ARST_VALUE = 0;

input CLK, ARST;
input [WIDTH-1:0] D;
output [WIDTH-1:0] Q;

genvar i;
generate
	for (i = 0; i < WIDTH; i = i + 1) begin:V
		if (CLK_POLARITY == 0 && ARST_POLARITY == 0 && ARST_VALUE[i] == 0) begin:NN0
			 \$_DFF_NN0_ ff (
				.D(D[i]),
				.Q(Q[i]),
				.C(CLK),
				.R(ARST)
			);
		end
		if (CLK_POLARITY == 0 && ARST_POLARITY == 0 && ARST_VALUE[i] != 0) begin:NN1
			 \$_DFF_NN1_ ff (
				.D(D[i]),
				.Q(Q[i]),
				.C(CLK),
				.R(ARST)
			);
		end
		if (CLK_POLARITY == 0 && ARST_POLARITY != 0 && ARST_VALUE[i] == 0) begin:NP0
			 \$_DFF_NP0_ ff (
				.D(D[i]),
				.Q(Q[i]),
				.C(CLK),
				.R(ARST)
			);
		end
		if (CLK_POLARITY == 0 && ARST_POLARITY != 0 && ARST_VALUE[i] != 0) begin:NP1
			 \$_DFF_NP1_ ff (
				.D(D[i]),
				.Q(Q[i]),
				.C(CLK),
				.R(ARST)
			);
		end
		if (CLK_POLARITY != 0 && ARST_POLARITY == 0 && ARST_VALUE[i] == 0) begin:PN0
			 \$_DFF_PN0_ ff (
				.D(D[i]),
				.Q(Q[i]),
				.C(CLK),
				.R(ARST)
			);
		end
		if (CLK_POLARITY != 0 && ARST_POLARITY == 0 && ARST_VALUE[i] != 0) begin:PN1
			 \$_DFF_PN1_ ff (
				.D(D[i]),
				.Q(Q[i]),
				.C(CLK),
				.R(ARST)
			);
		end
		if (CLK_POLARITY != 0 && ARST_POLARITY != 0 && ARST_VALUE[i] == 0) begin:PP0
			 \$_DFF_PP0_ ff (
				.D(D[i]),
				.Q(Q[i]),
				.C(CLK),
				.R(ARST)
			);
		end
		if (CLK_POLARITY != 0 && ARST_POLARITY != 0 && ARST_VALUE[i] != 0) begin:PP1
			 \$_DFF_PP1_ ff (
				.D(D[i]),
				.Q(Q[i]),
				.C(CLK),
				.R(ARST)
			);
		end
	end
endgenerate

endmodule

// --------------------------------------------------------

