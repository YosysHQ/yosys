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
				CARRY4 #(.IS_INITIALIZED(1'd1)) carry4_1st_part
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
				CARRY4 #(.IS_INITIALIZED(1'd1)) carry4_1st_full
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

	wire [Y_WIDTH-1:0] S = AA ^ BB;
	wire [Y_WIDTH-1:0] DI = AA & BB;

	wire CINIT;
	// Carry chain.
	//
	// VPR requires that the carry chain never hit the fabric.	The CO input
	// to this techmap is the carry outputs for synthesis, e.g. might hit the
	// fabric.
	//
	// So we maintain two wire sets, CO_CHAIN is the carry that is for VPR,
	// e.g. off fabric dedicated chain.  CO is the carry outputs that are
	// available to the fabric.
	wire [Y_WIDTH-1:0] CO_CHAIN;
	wire [Y_WIDTH-1:0] C = {CO_CHAIN, CINIT};

	// If carry chain is being initialized to a constant, techmap the constant
	// source.	Otherwise techmap the fabric source.
	generate for (i = 0; i < 1; i = i + 1) begin:slice
		CARRY0 #(.CYINIT_FABRIC(1)) carry(
			.CI_INIT(CI),
			.DI(DI[0]),
			.S(S[0]),
			.CO_CHAIN(CO_CHAIN[0]),
			.CO_FABRIC(CO[0]),
			.O(Y[0])
		);
	end endgenerate

	generate for (i = 1; i < Y_WIDTH-1; i = i + 1) begin:slice
		if(i % 4 == 0) begin
			CARRY0 carry (
				.CI(C[i]),
				.DI(DI[i]),
				.S(S[i]),
				.CO_CHAIN(CO_CHAIN[i]),
				.CO_FABRIC(CO[i]),
				.O(Y[i])
			);
		end
		else
		begin
			CARRY carry (
				.CI(C[i]),
				.DI(DI[i]),
				.S(S[i]),
				.CO_CHAIN(CO_CHAIN[i]),
				.CO_FABRIC(CO[i]),
				.O(Y[i])
			);
		end
	end endgenerate

	generate for (i = Y_WIDTH-1; i < Y_WIDTH; i = i + 1) begin:slice
		if(i % 4 == 0) begin
			CARRY0 top_of_carry (
				.CI(C[i]),
				.DI(DI[i]),
				.S(S[i]),
				.CO_CHAIN(CO_CHAIN[i]),
				.O(Y[i])
			);
		end
		else
		begin
			CARRY top_of_carry (
				.CI(C[i]),
				.DI(DI[i]),
				.S(S[i]),
				.CO_CHAIN(CO_CHAIN[i]),
				.O(Y[i])
			);
		end
		// Turns out CO_FABRIC and O both use [ABCD]MUX, so provide
		// a non-congested path to output the top of the carry chain.
		// Registering the output of the CARRY block would solve this, but not
		// all designs do that.
		if((i+1) % 4 == 0) begin
			CARRY0 carry_output (
				.CI(CO_CHAIN[i]),
				.DI(0),
				.S(0),
				.O(CO[i])
			);
		end
		else
		begin
			CARRY carry_output (
				.CI(CO_CHAIN[i]),
				.DI(0),
				.S(0),
				.O(CO[i])
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

