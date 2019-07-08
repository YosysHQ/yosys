// From Eddie Hung
// extracted from: https://github.com/eddiehung/vtr-with-yosys/blob/vtr7-with-yosys/vtr_flow/misc/yosys_models.v#L220
// revised by Andre DeHon
// further revised by David Shah
`ifndef DSP_A_MAXWIDTH
`define DSP_A_MAXWIDTH 18
`endif
`ifndef DSP_A_MAXWIDTH
`define DSP_B_MAXWIDTH 25
`endif

`ifndef ADDER_MINWIDTH
`define ADDER_MINWIDTH AAA
`endif

`ifndef DSP_NAME
`define DSP_NAME M18x25
`endif

`define MAX(a,b) (a > b ? a : b)
`define MIN(a,b) (a < b ? a : b)

(* techmap_celltype = "$mul" *)
module \$mul (A, B, Y); 
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] Y;

	wire [1023:0] _TECHMAP_DO_ = "proc; clean";

  generate
    if (A_WIDTH<B_WIDTH) begin
	generate
		\$__mul_gen #(
			.A_SIGNED(A_SIGNED),
			.B_SIGNED(B_SIGNED),
			.A_WIDTH(A_WIDTH),
			.B_WIDTH(B_WIDTH),
			.Y_WIDTH(Y_WIDTH)
		) mul_slice (
			.A(A),
			.B(B),
			.Y(Y[Y_WIDTH-1:0])
		);
	endgenerate
	end
    else begin
	generate
		\$__mul_gen #(
			.A_SIGNED(B_SIGNED),
			.B_SIGNED(A_SIGNED),
			.A_WIDTH(B_WIDTH),
			.B_WIDTH(A_WIDTH),
			.Y_WIDTH(Y_WIDTH)
		) mul_slice (
			.A(B),
			.B(A),
			.Y(Y[Y_WIDTH-1:0])
		);
	endgenerate
     end
   endgenerate	
endmodule

module \$__mul_gen (A, B, Y);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] Y;

	wire [1023:0] _TECHMAP_DO_ = "proc; clean";

	generate
	if (A_WIDTH > `DSP_A_MAXWIDTH) begin
			localparam n_floored = A_WIDTH/`DSP_A_MAXWIDTH;
			localparam n = n_floored + (n_floored*`DSP_A_MAXWIDTH < A_WIDTH ? 1 : 0);
			wire [`DSP_A_MAXWIDTH+B_WIDTH-1:0] partial [n-1:1];
			wire [Y_WIDTH-1:0] partial_sum [n-2:0];

			\$__mul_gen #(
				.A_SIGNED(A_SIGNED),
				.B_SIGNED(B_SIGNED),
				.A_WIDTH(`DSP_A_MAXWIDTH),
				.B_WIDTH(B_WIDTH),
				.Y_WIDTH(B_WIDTH+`DSP_A_MAXWIDTH)
			) mul_slice_first (
				.A(A[`DSP_A_MAXWIDTH-1:0]),
				.B(B),
				.Y(partial_sum[0][B_WIDTH+`DSP_A_MAXWIDTH-1:0])
			);
                        assign partial_sum[0][Y_WIDTH-1:B_WIDTH+`DSP_A_MAXWIDTH]=0;

			genvar i;
			generate
			for (i = 1; i < n-1; i=i+1) begin:slice
				\$__mul_gen #(
					.A_SIGNED(A_SIGNED),
					.B_SIGNED(B_SIGNED),
					.A_WIDTH(`DSP_A_MAXWIDTH),
					.B_WIDTH(B_WIDTH),
					.Y_WIDTH(B_WIDTH+`DSP_A_MAXWIDTH)
				) mul_slice (
					.A(A[(i+1)*`DSP_A_MAXWIDTH-1:i*`DSP_A_MAXWIDTH]),
					.B(B),
					.Y(partial[i][B_WIDTH+`DSP_A_MAXWIDTH-1:0])
				);
				//assign partial_sum[i] = (partial[i] << i*`DSP_A_MAXWIDTH) + partial_sum[i-1];
				assign partial_sum[i] = {
					partial[i][B_WIDTH+`DSP_A_MAXWIDTH-1:0]
					+ partial_sum[i-1][Y_WIDTH-1:(i*`DSP_A_MAXWIDTH)],
					partial_sum[i-1][(i*`DSP_A_MAXWIDTH)-1:0]
				};
			end
			endgenerate

			\$__mul_gen #(
				.A_SIGNED(A_SIGNED),
				.B_SIGNED(B_SIGNED),
				.A_WIDTH(A_WIDTH-(n-1)*`DSP_A_MAXWIDTH),
				.B_WIDTH(B_WIDTH),
				.Y_WIDTH(A_WIDTH-(n-1)*`DSP_A_MAXWIDTH+B_WIDTH),
			) mul_slice_last (
				.A(A[A_WIDTH-1:(n-1)*`DSP_A_MAXWIDTH]),
				.B(B),
				.Y(partial[n-1][A_WIDTH-(n-1)*`DSP_A_MAXWIDTH+B_WIDTH-1:0])
			);
			//assign Y = (partial[n-1] << (n-1)*`DSP_A_MAXWIDTH) + partial_sum[n-2];
			assign Y = {
				partial[n-1][A_WIDTH-(n-1)*`DSP_A_MAXWIDTH+B_WIDTH:0]
				+ partial_sum[n-2][Y_WIDTH-1:((n-1)*`DSP_A_MAXWIDTH)],
				partial_sum[n-2][((n-1)*`DSP_A_MAXWIDTH)-1:0]
			};
		end
		else if (B_WIDTH > `DSP_B_MAXWIDTH) begin
			localparam n_floored = B_WIDTH/`DSP_B_MAXWIDTH;
			localparam n = n_floored + (n_floored*`DSP_B_MAXWIDTH < B_WIDTH ? 1 : 0);
			wire [A_WIDTH+`DSP_B_MAXWIDTH-1:0] partial [n-1:1];
			wire [Y_WIDTH-1:0] partial_sum [n-2:0];

			\$__mul_gen #(
				.A_SIGNED(A_SIGNED),
				.B_SIGNED(B_SIGNED),
				.A_WIDTH(A_WIDTH),
				.B_WIDTH(`DSP_B_MAXWIDTH),
				.Y_WIDTH(A_WIDTH+`DSP_B_MAXWIDTH)
			) mul_first (
				.A(A),
				.B(B[`DSP_B_MAXWIDTH-1:0]),
				.Y(partial_sum[0][A_WIDTH+`DSP_B_MAXWIDTH-1:0])
			);
                        assign partial_sum[0][Y_WIDTH-1:A_WIDTH+`DSP_B_MAXWIDTH]=0;

			genvar i;
			generate
			for (i = 1; i < n-1; i=i+1) begin:slice
				\$__mul_gen #(
					.A_SIGNED(A_SIGNED),
					.B_SIGNED(B_SIGNED),
					.A_WIDTH(A_WIDTH),
					.B_WIDTH(`DSP_B_MAXWIDTH),
				        .Y_WIDTH(A_WIDTH+`DSP_B_MAXWIDTH)
				) mul (
					.A(A),
					.B(B[(i+1)*`DSP_B_MAXWIDTH-1:i*`DSP_B_MAXWIDTH]),
					.Y(partial[i][A_WIDTH+`DSP_B_MAXWIDTH-1:0])
				);
				//assign partial_sum[i] = (partial[i] << i*`DSP_B_MAXWIDTH) + partial_sum[i-1];
                                // was:
				//assign partial_sum[i] = {
				//  partial[i][A_WIDTH+`DSP_B_MAXWIDTH-1:`DSP_B_MAXWIDTH], 
				//	partial[i][`DSP_B_MAXWIDTH-1:0] + partial_sum[i-1][A_WIDTH+(i*`DSP_B_MAXWIDTH)-1:A_WIDTH+((i-1)*`DSP_B_MAXWIDTH)],
				//	partial_sum[i-1][A_WIDTH+((i-1)*`DSP_B_MAXWIDTH):0]
				assign partial_sum[i] = {
					partial[i][A_WIDTH+`DSP_B_MAXWIDTH-1:0]
					+ partial_sum[i-1][Y_WIDTH-1:(i*`DSP_B_MAXWIDTH)],
					partial_sum[i-1][(i*`DSP_B_MAXWIDTH)-1:0] 
				};
			end
			endgenerate

			\$__mul_gen #(
				.A_SIGNED(A_SIGNED),
				.B_SIGNED(B_SIGNED),
				.A_WIDTH(A_WIDTH),
				.B_WIDTH(B_WIDTH-(n-1)*`DSP_B_MAXWIDTH),
				.Y_WIDTH(A_WIDTH+B_WIDTH-(n-1)*`DSP_B_MAXWIDTH)
			) mul_last (
				.A(A),
				.B(B[B_WIDTH-1:(n-1)*`DSP_B_MAXWIDTH]),
				.Y(partial[n-1][A_WIDTH+B_WIDTH-(n-1)*`DSP_B_MAXWIDTH-1:0])
			);
                        // AMD: this came comment out -- looks closer to right answer
			//assign Y = (partial[n-1] << (n-1)*`DSP_B_MAXWIDTH) + partial_sum[n-2];
                        // was (looks broken)
			//assign Y = {
			//	partial[n-1][A_WIDTH+`DSP_B_MAXWIDTH-1:`DSP_B_MAXWIDTH],
			//	partial[n-1][`DSP_B_MAXWIDTH-1:0] + partial_sum[n-2][A_WIDTH+((n-1)*`DSP_B_MAXWIDTH)-1:A_WIDTH+((n-2)*`DSP_B_MAXWIDTH)],
			//	partial_sum[n-2][A_WIDTH+((n-2)*`DSP_B_MAXWIDTH):0]
                       assign Y = {
				partial[n-1][A_WIDTH+B_WIDTH-(n-1)*`DSP_B_MAXWIDTH-1:0]
				+ partial_sum[n-2][Y_WIDTH-1:((n-1)*`DSP_B_MAXWIDTH)],
				partial_sum[n-2][((n-1)*`DSP_B_MAXWIDTH)-1:0]
			};
		end
		else begin 
			wire [A_WIDTH+B_WIDTH-1:0] out;
			wire [(`DSP_A_MAXWIDTH+`DSP_B_MAXWIDTH)-(A_WIDTH+B_WIDTH)-1:0] dummy;
			wire Asign, Bsign;
			assign Asign = (A_SIGNED ? A[A_WIDTH-1] : 1'b0);
			assign Bsign = (B_SIGNED ? B[B_WIDTH-1] : 1'b0);
			`DSP_NAME _TECHMAP_REPLACE_ (
				.A({ {{`DSP_A_MAXWIDTH-A_WIDTH}{Asign}}, A }),
				.B({ {{`DSP_B_MAXWIDTH-B_WIDTH}{Bsign}}, B }),
				.OUT({dummy, out})
			);
			if (Y_WIDTH < A_WIDTH+B_WIDTH)
				assign Y = out[Y_WIDTH-1:0];
			else begin
				wire Ysign = (A_SIGNED || B_SIGNED ? out[A_WIDTH+BWIDTH-1] : 1'b0);
				assign Y = { {{Y_WIDTH-(A_WIDTH+B_WIDTH)}{Ysign}}, out[A_WIDTH+B_WIDTH-1:0] };
			end
		end
	endgenerate
endmodule


