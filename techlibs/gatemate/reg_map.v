/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2021  Cologne Chip AG <support@colognechip.com>
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

(* techmap_celltype = "$_DFFE_[NP][NP][01][NP]_" *)
module \$_DFFE_xxxx_ (input D, C, R, E, output Q);

	parameter _TECHMAP_CELLTYPE_ = "";
	parameter _TECHMAP_WIREINIT_Q_ = 1'bx;

	CC_DFF #(
		.CLK_INV(_TECHMAP_CELLTYPE_[39:32] == "N"),
		.EN_INV(_TECHMAP_CELLTYPE_[15:8] == "N"),
		.SR_INV(_TECHMAP_CELLTYPE_[31:24] == "N"),
		.SR_VAL(_TECHMAP_CELLTYPE_[23:16] == "1"),
		.INIT(_TECHMAP_WIREINIT_Q_)
	) _TECHMAP_REPLACE_ (.D(D), .EN(E), .CLK(C), .SR(R), .Q(Q));

	wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule

(* techmap_celltype = "$_DLATCH_[NP][NP][01]_" *)
module \$_DLATCH_xxx_ (input E, R, D, output Q);

	parameter _TECHMAP_CELLTYPE_ = "";
	parameter _TECHMAP_WIREINIT_Q_ = 1'bx;

	CC_DLT #(
		.G_INV(_TECHMAP_CELLTYPE_[31:24] == "N"),
		.SR_INV(_TECHMAP_CELLTYPE_[23:16] == "N"),
		.SR_VAL(_TECHMAP_CELLTYPE_[15:8] == "1"),
		.INIT(_TECHMAP_WIREINIT_Q_)
	) _TECHMAP_REPLACE_ (.D(D), .G(E), .SR(R), .Q(Q));

	wire _TECHMAP_REMOVEINIT_Q_ = 1;
endmodule
