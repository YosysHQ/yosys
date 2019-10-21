/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *                2019  Eddie Hung    <eddie@fpgeh.com>
 *                2019  David Shah    <dave@ds0.me>
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
 *  Tech-mapping rules for decomposing arbitrarily-sized $mul cells
 *  into an equivalent collection of smaller `DSP_NAME cells (with the 
 *  same interface as $mul) no larger than `DSP_[AB]_MAXWIDTH, attached 
 *  to $shl and $add cells.
 *
 */

`ifndef DSP_A_MAXWIDTH
$fatal(1, "Macro DSP_A_MAXWIDTH must be defined");
`endif
`ifndef DSP_B_MAXWIDTH
$fatal(1, "Macro DSP_B_MAXWIDTH must be defined");
`endif
`ifndef DSP_B_MAXWIDTH
$fatal(1, "Macro DSP_B_MAXWIDTH must be defined");
`endif
`ifndef DSP_A_MAXWIDTH_PARTIAL
`define DSP_A_MAXWIDTH_PARTIAL `DSP_A_MAXWIDTH
`endif
`ifndef DSP_B_MAXWIDTH_PARTIAL
`define DSP_B_MAXWIDTH_PARTIAL `DSP_B_MAXWIDTH
`endif

`ifndef DSP_NAME
$fatal(1, "Macro DSP_NAME must be defined");
`endif

`define MAX(a,b) (a > b ? a : b)
`define MIN(a,b) (a < b ? a : b)

(* techmap_celltype = "$mul $__mul" *)
module _80_mul (A, B, Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] Y;

	parameter _TECHMAP_CELLTYPE_ = "";

	generate
	if (0) begin end
`ifdef DSP_A_MINWIDTH
	else if (A_WIDTH < `DSP_A_MINWIDTH)
		wire _TECHMAP_FAIL_ = 1;
`endif
`ifdef DSP_B_MINWIDTH
	else if (B_WIDTH < `DSP_B_MINWIDTH)
		wire _TECHMAP_FAIL_ = 1;
`endif
`ifdef DSP_Y_MINWIDTH
	else if (Y_WIDTH < `DSP_Y_MINWIDTH)
		wire _TECHMAP_FAIL_ = 1;
`endif
`ifdef DSP_SIGNEDONLY
	else if (_TECHMAP_CELLTYPE_ == "$mul" && !A_SIGNED && !B_SIGNED)
		\$mul #(
			.A_SIGNED(1),
			.B_SIGNED(1),
			.A_WIDTH(A_WIDTH + 1),
			.B_WIDTH(B_WIDTH + 1),
			.Y_WIDTH(Y_WIDTH)
		) _TECHMAP_REPLACE_ (
			.A({1'b0, A}),
			.B({1'b0, B}),
			.Y(Y)
		);
`endif
	else if (_TECHMAP_CELLTYPE_ == "$mul" && A_WIDTH < B_WIDTH)
		\$mul #(
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
	else begin
		wire [1023:0] _TECHMAP_DO_ = "proc; clean";

`ifdef DSP_SIGNEDONLY
		localparam sign_headroom = 1;
`else
		localparam sign_headroom = 0;
`endif

		genvar i;
		if (A_WIDTH > `DSP_A_MAXWIDTH) begin
			localparam n = (A_WIDTH-`DSP_A_MAXWIDTH+`DSP_A_MAXWIDTH_PARTIAL-sign_headroom-1) / (`DSP_A_MAXWIDTH_PARTIAL-sign_headroom);
			localparam partial_Y_WIDTH = `MIN(Y_WIDTH, B_WIDTH+`DSP_A_MAXWIDTH_PARTIAL);
			localparam last_A_WIDTH = A_WIDTH-n*(`DSP_A_MAXWIDTH_PARTIAL-sign_headroom);
			localparam last_Y_WIDTH = B_WIDTH+last_A_WIDTH;
			if (A_SIGNED && B_SIGNED) begin
				wire signed [partial_Y_WIDTH-1:0] partial [n-1:0];
				wire signed [last_Y_WIDTH-1:0] last_partial;
				wire signed [Y_WIDTH-1:0] partial_sum [n:0];
			end
			else begin
				wire [partial_Y_WIDTH-1:0] partial [n-1:0];
				wire [last_Y_WIDTH-1:0] last_partial;
				wire [Y_WIDTH-1:0] partial_sum [n:0];
			end

			for (i = 0; i < n; i=i+1) begin:sliceA
				\$__mul #(
					.A_SIGNED(sign_headroom),
					.B_SIGNED(B_SIGNED),
					.A_WIDTH(`DSP_A_MAXWIDTH_PARTIAL),
					.B_WIDTH(B_WIDTH),
					.Y_WIDTH(partial_Y_WIDTH)
				) mul (
					.A({{sign_headroom{1'b0}}, A[i*(`DSP_A_MAXWIDTH_PARTIAL-sign_headroom) +: `DSP_A_MAXWIDTH_PARTIAL-sign_headroom]}),
					.B(B),
					.Y(partial[i])
				);
				// TODO: Currently a 'cascade' approach to summing the partial
				//       products is taken here, but a more efficient 'binary
				//       reduction' approach also exists...
				if (i == 0)
					assign partial_sum[i] = partial[i];
				else
					assign partial_sum[i] = (partial[i] << (* mul2dsp *) i*(`DSP_A_MAXWIDTH_PARTIAL-sign_headroom)) + (* mul2dsp *) partial_sum[i-1];
			end

			\$__mul #(
				.A_SIGNED(A_SIGNED),
				.B_SIGNED(B_SIGNED),
				.A_WIDTH(last_A_WIDTH),
				.B_WIDTH(B_WIDTH),
				.Y_WIDTH(last_Y_WIDTH)
			) sliceA.last (
				.A(A[A_WIDTH-1 -: last_A_WIDTH]),
				.B(B),
				.Y(last_partial)
			);
			assign partial_sum[n] = (last_partial << (* mul2dsp *) n*(`DSP_A_MAXWIDTH_PARTIAL-sign_headroom)) + (* mul2dsp *) partial_sum[n-1];
			assign Y = partial_sum[n];
		end
		else if (B_WIDTH > `DSP_B_MAXWIDTH) begin
			localparam n = (B_WIDTH-`DSP_B_MAXWIDTH+`DSP_B_MAXWIDTH_PARTIAL-sign_headroom-1) / (`DSP_B_MAXWIDTH_PARTIAL-sign_headroom);
			localparam partial_Y_WIDTH = `MIN(Y_WIDTH, A_WIDTH+`DSP_B_MAXWIDTH_PARTIAL);
			localparam last_B_WIDTH = B_WIDTH-n*(`DSP_B_MAXWIDTH_PARTIAL-sign_headroom);
			localparam last_Y_WIDTH = A_WIDTH+last_B_WIDTH;
			if (A_SIGNED && B_SIGNED) begin
				wire signed [partial_Y_WIDTH-1:0] partial [n-1:0];
				wire signed [last_Y_WIDTH-1:0] last_partial;
				wire signed [Y_WIDTH-1:0] partial_sum [n:0];
			end
			else begin
				wire [partial_Y_WIDTH-1:0] partial [n-1:0];
				wire [last_Y_WIDTH-1:0] last_partial;
				wire [Y_WIDTH-1:0] partial_sum [n:0];
			end

			for (i = 0; i < n; i=i+1) begin:sliceB
				\$__mul #(
					.A_SIGNED(A_SIGNED),
					.B_SIGNED(sign_headroom),
					.A_WIDTH(A_WIDTH),
					.B_WIDTH(`DSP_B_MAXWIDTH_PARTIAL),
					.Y_WIDTH(partial_Y_WIDTH)
				) mul (
					.A(A),
					.B({{sign_headroom{1'b0}}, B[i*(`DSP_B_MAXWIDTH_PARTIAL-sign_headroom) +: `DSP_B_MAXWIDTH_PARTIAL-sign_headroom]}),
					.Y(partial[i])
				);
				// TODO: Currently a 'cascade' approach to summing the partial
				//       products is taken here, but a more efficient 'binary
				//       reduction' approach also exists...
				if (i == 0)
					assign partial_sum[i] = partial[i];
				else
					assign partial_sum[i] = (partial[i] << (* mul2dsp *) i*(`DSP_B_MAXWIDTH_PARTIAL-sign_headroom)) + (* mul2dsp *) partial_sum[i-1];
			end

			\$__mul #(
				.A_SIGNED(A_SIGNED),
				.B_SIGNED(B_SIGNED),
				.A_WIDTH(A_WIDTH),
				.B_WIDTH(last_B_WIDTH),
				.Y_WIDTH(last_Y_WIDTH)
			) mul_sliceB_last (
				.A(A),
				.B(B[B_WIDTH-1 -: last_B_WIDTH]),
				.Y(last_partial)
			);
			assign partial_sum[n] = (last_partial << (* mul2dsp *) n*(`DSP_B_MAXWIDTH_PARTIAL-sign_headroom)) + (* mul2dsp *) partial_sum[n-1];
			assign Y = partial_sum[n];
		end
		else begin
			if (A_SIGNED)
				wire signed [`DSP_A_MAXWIDTH-1:0] Aext = $signed(A);
			else
				wire [`DSP_A_MAXWIDTH-1:0] Aext = A;
			if (B_SIGNED)
				wire signed [`DSP_B_MAXWIDTH-1:0] Bext = $signed(B);
			else
				wire [`DSP_B_MAXWIDTH-1:0] Bext = B;

			`DSP_NAME #(
				.A_SIGNED(A_SIGNED),
				.B_SIGNED(B_SIGNED),
				.A_WIDTH(`DSP_A_MAXWIDTH),
				.B_WIDTH(`DSP_B_MAXWIDTH),
				.Y_WIDTH(`MIN(Y_WIDTH,`DSP_A_MAXWIDTH+`DSP_B_MAXWIDTH)),
			) _TECHMAP_REPLACE_ (
				.A(Aext),
				.B(Bext),
				.Y(Y)
			);
		end
	end
	endgenerate
endmodule

(* techmap_celltype = "$mul $__mul" *)
module _90_soft_mul (A, B, Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] Y;

	// Indirection necessary since mapping
	//   back to $mul will cause recursion
	generate
	if (A_SIGNED && !B_SIGNED)
		\$__soft_mul #(
			.A_SIGNED(A_SIGNED),
			.B_SIGNED(1),
			.A_WIDTH(A_WIDTH),
			.B_WIDTH(B_WIDTH+1),
			.Y_WIDTH(Y_WIDTH)
		) _TECHMAP_REPLACE_ (
			.A(A),
			.B({1'b0,B}),
			.Y(Y)
		);
	else if (!A_SIGNED && B_SIGNED)
		\$__soft_mul #(
			.A_SIGNED(1),
			.B_SIGNED(B_SIGNED),
			.A_WIDTH(A_WIDTH+1),
			.B_WIDTH(B_WIDTH),
			.Y_WIDTH(Y_WIDTH)
		) _TECHMAP_REPLACE_ (
			.A({1'b0,A}),
			.B(B),
			.Y(Y)
		);
	else
		\$__soft_mul #(
			.A_SIGNED(A_SIGNED),
			.B_SIGNED(B_SIGNED),
			.A_WIDTH(A_WIDTH),
			.B_WIDTH(B_WIDTH),
			.Y_WIDTH(Y_WIDTH)
		) _TECHMAP_REPLACE_ (
			.A(A),
			.B(B),
			.Y(Y)
		);
	endgenerate
endmodule
