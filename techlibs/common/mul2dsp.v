// From Eddie Hung
// extracted from: https://github.com/eddiehung/vtr-with-yosys/blob/vtr7-with-yosys/vtr_flow/misc/yosys_models.v#L220
// revised by Andre DeHon
// further revised by David Shah
`ifndef DSP_A_MAXWIDTH
$error("Macro DSP_A_MAXWIDTH must be defined");
`endif
`ifndef DSP_B_MAXWIDTH
$error("Macro DSP_B_MAXWIDTH must be defined");
`endif

`ifndef DSP_NAME
$error("Macro DSP_NAME must be defined");
`endif

`define MAX(a,b) (a > b ? a : b)
`define MIN(a,b) (a < b ? a : b)

module \$mul (A, B, Y); 
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] Y;

	generate
	if (A_SIGNED != B_SIGNED)
		wire _TECHMAP_FAIL_ = 1;
	else if (A_WIDTH <= `DSP_A_MAXWIDTH && B_WIDTH <= `DSP_B_MAXWIDTH)
		wire _TECHMAP_FAIL_ = 1;
	// NB: A_SIGNED == B_SIGNED == 0 from here
	else if (A_WIDTH >= B_WIDTH)
		\$__mul #(
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
	else
		\$__mul #(
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
	endgenerate
endmodule

module \$__mul (A, B, Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] Y;

	wire [1023:0] _TECHMAP_DO_ = "proc; clean";

`ifdef DSP_SIGNEDONLY
	localparam sign_headroom = 1;
`else
	localparam sign_headroom = 0;
`endif

	genvar i;
	generate
		if (A_WIDTH <= 1 || B_WIDTH <= 1)
			wire _TECHMAP_FAIL_ = 1;
`ifdef DSP_MINWIDTH
		else if (A_WIDTH+B_WIDTH < `DSP_MINWIDTH || Y_WIDTH < `DSP_MINWIDTH)
			wire _TECHMAP_FAIL_ = 1;
`endif
		else if (A_WIDTH > `DSP_A_MAXWIDTH) begin
			localparam n = (A_WIDTH+`DSP_A_MAXWIDTH-sign_headroom-1) / (`DSP_A_MAXWIDTH-sign_headroom);
			localparam partial_Y_WIDTH = `MIN(Y_WIDTH, B_WIDTH+`DSP_A_MAXWIDTH);
			if (A_SIGNED && B_SIGNED) begin
				wire signed [partial_Y_WIDTH-1:0] partial [n-1:0];
				wire signed [Y_WIDTH-1:0] partial_sum [n-1:0];
			end
			else begin
				wire [partial_Y_WIDTH-1:0] partial [n-1:0];
				wire [Y_WIDTH-1:0] partial_sum [n-1:0];
			end

			\$__mul #(
				.A_SIGNED(sign_headroom),
				.B_SIGNED(B_SIGNED),
				.A_WIDTH(`DSP_A_MAXWIDTH),
				.B_WIDTH(B_WIDTH),
				.Y_WIDTH(partial_Y_WIDTH)
			) mul_slice_first (
				.A({{sign_headroom{1'b0}}, A[`DSP_A_MAXWIDTH-sign_headroom-1 : 0]}),
				.B(B),
				.Y(partial[0])
			);
			assign partial_sum[0] = partial[0];

			for (i = 1; i < n-1; i=i+1) begin:slice
				\$__mul #(
					.A_SIGNED(sign_headroom),
					.B_SIGNED(B_SIGNED),
					.A_WIDTH(`DSP_A_MAXWIDTH),
					.B_WIDTH(B_WIDTH),
					.Y_WIDTH(partial_Y_WIDTH)
				) mul_slice (
					.A({{sign_headroom{1'b0}}, A[i*(`DSP_A_MAXWIDTH-sign_headroom) +: `DSP_A_MAXWIDTH-sign_headroom]}),
					.B(B),
					.Y(partial[i])
				);
				assign partial_sum[i] = (partial[i] << i*(`DSP_A_MAXWIDTH-sign_headroom)) + partial_sum[i-1];
			end

			\$__mul #(
				.A_SIGNED(A_SIGNED),
				.B_SIGNED(B_SIGNED),
				.A_WIDTH(A_WIDTH-(n-1)*(`DSP_A_MAXWIDTH-sign_headroom)),
				.B_WIDTH(B_WIDTH),
				.Y_WIDTH(partial_Y_WIDTH)
			) mul_slice_last (
				.A(A[A_WIDTH-1 : (n-1)*(`DSP_A_MAXWIDTH-sign_headroom)]),
				.B(B),
				.Y(partial[n-1])
			);
			assign partial_sum[n-1] = (partial[n-1] << (n-1)*(`DSP_A_MAXWIDTH-sign_headroom)) + partial_sum[n-2];
			assign Y = partial_sum[n-1];
		end
		else if (B_WIDTH > `DSP_B_MAXWIDTH) begin
			localparam n = (B_WIDTH+`DSP_B_MAXWIDTH-sign_headroom-1) / (`DSP_B_MAXWIDTH-sign_headroom);
			localparam partial_Y_WIDTH = `MIN(Y_WIDTH, A_WIDTH+`DSP_B_MAXWIDTH);
			if (A_SIGNED && B_SIGNED) begin
				wire signed [partial_Y_WIDTH-1:0] partial [n-1:0];
				wire signed [Y_WIDTH-1:0] partial_sum [n-1:0];
			end
			else begin
				wire [partial_Y_WIDTH-1:0] partial [n-1:0];
				wire [Y_WIDTH-1:0] partial_sum [n-1:0];
			end

			\$__mul #(
				.A_SIGNED(A_SIGNED),
				.B_SIGNED(sign_headroom),
				.A_WIDTH(A_WIDTH),
				.B_WIDTH(`DSP_B_MAXWIDTH),
				.Y_WIDTH(partial_Y_WIDTH)
			) mul_first (
				.A(A),
				.B({{sign_headroom{1'b0}}, B[`DSP_B_MAXWIDTH-sign_headroom-1 : 0]}),
				.Y(partial[0])
			);
			assign partial_sum[0] = partial[0];

			for (i = 1; i < n-1; i=i+1) begin:slice
				\$__mul #(
					.A_SIGNED(A_SIGNED),
					.B_SIGNED(sign_headroom),
					.A_WIDTH(A_WIDTH),
					.B_WIDTH(`DSP_B_MAXWIDTH),
					.Y_WIDTH(partial_Y_WIDTH)
				) mul (
					.A(A),
					.B({{sign_headroom{1'b0}}, B[i*(`DSP_B_MAXWIDTH-sign_headroom) +: `DSP_B_MAXWIDTH-sign_headroom]}),
					.Y(partial[i])
				);
				assign partial_sum[i] = (partial[i] << i*(`DSP_B_MAXWIDTH-sign_headroom)) + partial_sum[i-1];
			end

			\$__mul #(
				.A_SIGNED(A_SIGNED),
				.B_SIGNED(B_SIGNED),
				.A_WIDTH(A_WIDTH),
				.B_WIDTH(B_WIDTH-(n-1)*(`DSP_B_MAXWIDTH-sign_headroom)),
				.Y_WIDTH(partial_Y_WIDTH)
			) mul_last (
				.A(A),
				.B(B[B_WIDTH-1 : (n-1)*(`DSP_B_MAXWIDTH-sign_headroom)]),
				.Y(partial[n-1])
			);
			assign partial_sum[n-1] = (partial[n-1] << (n-1)*(`DSP_B_MAXWIDTH-sign_headroom)) + partial_sum[n-2];
			assign Y = partial_sum[n-1];
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
	endgenerate
endmodule

(* techmap_celltype = "$__mul" *)
module _90_internal_mul_to_external (A, B, Y); 
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] Y;

	generate
		if (A_SIGNED && !B_SIGNED)
			\$mul #(
				.A_SIGNED(A_SIGNED),
				.B_SIGNED(1),
				.A_WIDTH(A_WIDTH),
				.B_WIDTH(B_WIDTH+1),
				.Y_WIDTH(Y_WIDTH)
			) _TECHMAP_REPLACE_ (
				.A(A),
				.B({1'b0, B}),
				.Y(Y)
			);
		else if (!A_SIGNED && B_SIGNED)
			\$mul #(
				.A_SIGNED(1),
				.B_SIGNED(B_SIGNED),
				.A_WIDTH(A_WIDTH+1),
				.B_WIDTH(B_WIDTH),
				.Y_WIDTH(Y_WIDTH)
			) _TECHMAP_REPLACE_ (
				.A({1'b0, A}),
				.B(B),
				.Y(Y)
			);
		else
			\$mul #(
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
