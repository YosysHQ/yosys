/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2024  Martin Povišer <povik@cutebit.org>
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

(* techmap_celltype = "$lcu" *)
module _80_lcu_kogge_stone (P, G, CI, CO);
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

		for (i = 0; i < $clog2(WIDTH); i = i + 1) begin
			// iterate in reverse so we don't confuse a result from this stage and the previous
			for (j = WIDTH - 1; j >= 2**i; j = j - 1) begin
				g[j] = g[j] | p[j] & g[j - 2**i];
				p[j] = p[j] & p[j - 2**i];
			end
		end
	end

	assign CO = g;
endmodule
