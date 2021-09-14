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

module \$__toutpad (input A, input OE, output O);
	CC_TOBUF /*#(
		.PIN_NAME("UNPLACED"),
		.V_IO("UNDEFINED"),
		.SLEW("UNDEFINED"),
		.DRIVE(1'bx),
		.PULLUP(1'bx),
		.PULLDOWN(1'bx),
		.KEEPER(1'bx),
		.DELAY_OBF(4'bx),
		.FF_OBF(1'bx)
	)*/ _TECHMAP_REPLACE_ (
		.A(A),
		.T(~OE),
		.O(O)
	);
endmodule

module \$__tinoutpad (input A, input OE, inout IO, output Y);
	CC_IOBUF /*#(
		.PIN_NAME("UNPLACED"),
		.V_IO("UNDEFINED"),
		.SLEW("UNDEFINED"),
		.DRIVE(1'bx),
		.PULLUP(1'bx),
		.PULLDOWN(1'bx),
		.KEEPER(1'bx),
		.SCHMITT_TRIGGER(1'bx),
		.DELAY_IBF(4'bx),
		.DELAY_OBF(4'bx),
		.FF_IBF(1'bx),
		.FF_OBF(1'bx)
	)*/ _TECHMAP_REPLACE_ (
		.A(A),
		.T(~OE),
		.IO(IO),
		.Y(Y)
	);
endmodule
