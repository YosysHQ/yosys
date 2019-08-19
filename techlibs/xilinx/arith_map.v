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
 */

// ============================================================================
// LCU

(* techmap_celltype = "$lcu" *)
module _80_xilinx_lcu (P, G, CI, CO);
	parameter WIDTH = 2;

	input [WIDTH-1:0] P, G;
	input CI;

	output [WIDTH-1:0] CO;

	wire _TECHMAP_FAIL_ = WIDTH <= 2;

	genvar i;

`ifdef _CLB_CARRY

	localparam CARRY4_COUNT = (WIDTH + 3) / 4;
	localparam MAX_WIDTH    = CARRY4_COUNT * 4;
	localparam PAD_WIDTH    = MAX_WIDTH - WIDTH;

	wire [MAX_WIDTH-1:0] S  = {{PAD_WIDTH{1'b0}}, P & ~G};
	wire [MAX_WIDTH-1:0] C  = CO;

	generate for (i = 0; i < CARRY4_COUNT; i = i + 1) begin:slice

		// Partially occupied CARRY4
		if ((i+1)*4 > WIDTH) begin

			// First one
			if (i == 0) begin
				CARRY4 carry4_1st_part
				(
				.CYINIT(CI),
				.CI    (1'd0),
				.DI    (G [(Y_WIDTH - 1):i*4]),
				.S     (S [(Y_WIDTH - 1):i*4]),
				.CO    (CO[(Y_WIDTH - 1):i*4]),
				);
			// Another one
			end else begin
				CARRY4 carry4_part
				(
				.CYINIT(1'd0),
				.CI    (C [i*4 - 1]),
				.DI    (G [(Y_WIDTH - 1):i*4]),
				.S     (S [(Y_WIDTH - 1):i*4]),
				.CO    (CO[(Y_WIDTH - 1):i*4]),
				);
			end

		// Fully occupied CARRY4
		end else begin

			// First one
			if (i == 0) begin
				CARRY4 carry4_1st_full
				(
				.CYINIT(CI),
				.CI    (1'd0),
				.DI    (G [((i+1)*4 - 1):i*4]),
				.S     (S [((i+1)*4 - 1):i*4]),
				.CO    (CO[((i+1)*4 - 1):i*4]),
				);
			// Another one
			end else begin
				CARRY4 carry4_full
				(
				.CYINIT(1'd0),
				.CI    (C [i*4 - 1]),
				.DI    (G [((i+1)*4 - 1):i*4]),
				.S     (S [((i+1)*4 - 1):i*4]),
				.CO    (CO[((i+1)*4 - 1):i*4]),
				);
			end

		end

	end endgenerate

`elsif _EXPLICIT_CARRY

	wire [WIDTH-1:0] C = {CO, CI};
	wire [WIDTH-1:0] S = P & ~G;

	generate for (i = 0; i < WIDTH; i = i + 1) begin:slice
		MUXCY muxcy (
			.CI(C[i]),
			.DI(G[i]),
			.S(S[i]),
			.O(CO[i])
		);
	end endgenerate

`else

	wire [WIDTH-1:0] C = {CO, CI};
	wire [WIDTH-1:0] S = P & ~G;

	generate for (i = 0; i < WIDTH; i = i + 1) begin:slice
		MUXCY muxcy (
			.CI(C[i]),
			.DI(G[i]),
			.S(S[i]),
			.O(CO[i])
		);
	end endgenerate
`endif

endmodule


// ============================================================================
// ALU

(* techmap_celltype = "$alu" *)
module _80_xilinx_alu (A, B, CI, BI, X, Y, CO);
	parameter A_SIGNED = 0;
	parameter B_SIGNED = 0;
	parameter A_WIDTH = 1;
	parameter B_WIDTH = 1;
	parameter Y_WIDTH = 1;
	parameter _TECHMAP_CONSTVAL_CI_ = 0;
	parameter _TECHMAP_CONSTMSK_CI_ = 0;

	input [A_WIDTH-1:0] A;
	input [B_WIDTH-1:0] B;
	output [Y_WIDTH-1:0] X, Y;

	input CI, BI;
	output [Y_WIDTH-1:0] CO;

	wire _TECHMAP_FAIL_ = Y_WIDTH <= 2;

	wire [Y_WIDTH-1:0] A_buf, B_buf;
	\$pos #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(Y_WIDTH)) A_conv (.A(A), .Y(A_buf));
	\$pos #(.A_SIGNED(B_SIGNED), .A_WIDTH(B_WIDTH), .Y_WIDTH(Y_WIDTH)) B_conv (.A(B), .Y(B_buf));

	wire [Y_WIDTH-1:0] AA = A_buf;
	wire [Y_WIDTH-1:0] BB = BI ? ~B_buf : B_buf;

	genvar i;

`ifdef _CLB_CARRY

	localparam CARRY4_COUNT = (Y_WIDTH + 3) / 4;
	localparam MAX_WIDTH    = CARRY4_COUNT * 4;
	localparam PAD_WIDTH    = MAX_WIDTH - Y_WIDTH;

	wire [MAX_WIDTH-1:0] S  = {{PAD_WIDTH{1'b0}}, AA ^ BB};
	wire [MAX_WIDTH-1:0] DI = {{PAD_WIDTH{1'b0}}, AA & BB};

	wire [MAX_WIDTH-1:0] C  = CO;

	genvar i;
	generate for (i = 0; i < CARRY4_COUNT; i = i + 1) begin:slice

		// Partially occupied CARRY4
		if ((i+1)*4 > Y_WIDTH) begin

			// First one
			if (i == 0) begin
				CARRY4 carry4_1st_part
				(
				.CYINIT(CI),
				.CI    (1'd0),
				.DI    (DI[(Y_WIDTH - 1):i*4]),
				.S     (S [(Y_WIDTH - 1):i*4]),
				.O     (Y [(Y_WIDTH - 1):i*4]),
				.CO    (CO[(Y_WIDTH - 1):i*4])
				);
			// Another one
			end else begin
				CARRY4 carry4_part
				(
				.CYINIT(1'd0),
				.CI    (C [i*4 - 1]),
				.DI    (DI[(Y_WIDTH - 1):i*4]),
				.S     (S [(Y_WIDTH - 1):i*4]),
				.O     (Y [(Y_WIDTH - 1):i*4]),
				.CO    (CO[(Y_WIDTH - 1):i*4])
				);
			end

		// Fully occupied CARRY4
		end else begin

			// First one
			if (i == 0) begin
				CARRY4 carry4_1st_full
				(
				.CYINIT(CI),
				.CI    (1'd0),
				.DI    (DI[((i+1)*4 - 1):i*4]),
				.S     (S [((i+1)*4 - 1):i*4]),
				.O     (Y [((i+1)*4 - 1):i*4]),
				.CO    (CO[((i+1)*4 - 1):i*4])
				);
			// Another one
			end else begin
				CARRY4 carry4_full
				(
				.CYINIT(1'd0),
				.CI    (C [i*4 - 1]),
				.DI    (DI[((i+1)*4 - 1):i*4]),
				.S     (S [((i+1)*4 - 1):i*4]),
				.O     (Y [((i+1)*4 - 1):i*4]),
				.CO    (CO[((i+1)*4 - 1):i*4])
				);
			end

		end

	end endgenerate

`elsif _EXPLICIT_CARRY

	// Turns out CO and O both use [ABCD]MUX, so provide a non-congested path
	// to carry chain by using O outputs.
	//
	// Registering the output of the CARRY block would prevent the need to do
	// this, but not all designs do that.
	//
	// To ensure that PAD_WIDTH > 0, add 1 to Y_WIDTH.
	localparam Y_PAD_WIDTH  = Y_WIDTH + 1;
	localparam CARRY4_COUNT = (Y_PAD_WIDTH + 3) / 4;
	localparam MAX_WIDTH    = CARRY4_COUNT * 4;
	localparam PAD_WIDTH    = MAX_WIDTH - Y_WIDTH;

	wire [Y_PAD_WIDTH-1:0] O;
	wire [MAX_WIDTH-1:0] S  = {{PAD_WIDTH{1'b0}}, AA ^ BB};
	wire [MAX_WIDTH-1:0] DI = {{PAD_WIDTH{1'b0}}, AA & BB};

	// Carry chain between CARRY4 blocks.
	//
	// VPR requires that the carry chain never hit the fabric. The CO input
	// to this techmap is the carry outputs for synthesis, e.g. might hit the
	// fabric.
	//
	// So we maintain two wire sets, CO_CHAIN is the carry that is for VPR,
	// e.g. off fabric dedicated chain.  CO is the carry outputs that are
	// available to the fabric.
	wire [CARRY4_COUNT-1:0] CO_CHAIN;
	wire [CARRY4_COUNT-1:0] CO_CHAIN_PLUG;

	assign Y[Y_WIDTH-1:0] = O[Y_WIDTH-1:0];

	// If the design needs access to intermediate carry values, use the O pin
	// (e.g. no other CARRY4 pin) to avoid [ABCD]MUX congestion.
	// This does result in the CARRY stack being one element higher, but it
	// avoids the need to deal with congestion at the top of the chain.
	//
	// Note:
	//
	//  O[N] = CO[N-1] ^ S[N]
	//
	// So for top of chain, S[N] = 0:
	//
	//  O[N] = CO[N-1]
	assign CO[Y_WIDTH-1:0] = O[Y_WIDTH:1] ^ S[Y_WIDTH:1];

	genvar i;
	generate for (i = 0; i < CARRY4_COUNT; i = i + 1) begin:slice

		// Partially occupied CARRY4
		if ((i+1)*4 > Y_PAD_WIDTH) begin

			// First one
			if (i == 0) begin
				CARRY4_COUT carry4_1st_part
				(
				.CYINIT(CI),
				.DI    (DI[(Y_PAD_WIDTH - 1):i*4]),
				.S     (S [(Y_PAD_WIDTH - 1):i*4]),
				.O     (O [(Y_PAD_WIDTH - 1):i*4]),
				);
			// Another one
			end else begin
				CARRY4_COUT carry4_part
				(
				.CI    (CO_CHAIN [i-1]),
				.DI    (DI[(Y_PAD_WIDTH - 1):i*4]),
				.S     (S [(Y_PAD_WIDTH - 1):i*4]),
				.O     (O [(Y_PAD_WIDTH - 1):i*4]),
				);
			end

		// Fully occupied CARRY4
		end else begin

			// First one
			if (i == 0) begin
				CARRY4_COUT carry4_1st_full
				(
				.CYINIT(CI),
				.DI    (DI[((i+1)*4 - 1):i*4]),
				.S     (S [((i+1)*4 - 1):i*4]),
				.O     (O [((i+1)*4 - 1):i*4]),
				.COUT(CO_CHAIN_PLUG[i])
				);
			// Another one
			end else begin
				CARRY4_COUT carry4_full
				(
				.CI    (CO_CHAIN[i-1]),
				.DI    (DI[((i+1)*4 - 1):i*4]),
				.S     (S [((i+1)*4 - 1):i*4]),
				.O     (O [((i+1)*4 - 1):i*4]),
				.COUT(CO_CHAIN_PLUG[i])
				);
			end

			CARRY_COUT_PLUG plug(
				.CIN(CO_CHAIN_PLUG[i]),
				.COUT(CO_CHAIN[i])
			);
		end

	end endgenerate

`else

	wire [Y_WIDTH-1:0] S = AA ^ BB;
	wire [Y_WIDTH-1:0] DI = AA & BB;

	wire [Y_WIDTH-1:0] C = {CO, CI};

	generate for (i = 0; i < Y_WIDTH; i = i + 1) begin:slice
		MUXCY muxcy (
			.CI(C[i]),
			.DI(DI[i]),
			.S(S[i]),
			.O(CO[i])
		);
		XORCY xorcy (
			.CI(C[i]),
			.LI(S[i]),
			.O(Y[i])
		);
	end endgenerate

`endif

	assign X = S;
endmodule

