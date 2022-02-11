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

module \$_MUX8_ (A, B, C, D, E, F, G, H, S, T, U, Y);
	input  A, B, C, D, E, F, G, H, S, T, U;
	output Y;

	CC_MX8 _TECHMAP_REPLACE_ (
		.D0(A), .D1(B), .D2(C), .D3(D),
		.D4(E), .D5(F), .D6(G), .D7(H),
		.S0(S), .S1(T), .S2(U),
		.Y(Y)
	);

endmodule

module \$_MUX4_ (A, B, C, D, S, T, Y);
	input  A, B, C, D, S, T;
	output Y;

	CC_MX4 _TECHMAP_REPLACE_ (
		.D0(A), .D1(B), .D2(C), .D3(D),
		.S0(S), .S1(T),
		.Y(Y)
	);

endmodule

/*
module \$_MUX_ (A, B, S, Y);
	input  A, B, S;
	output Y;

	CC_MX2 _TECHMAP_REPLACE_ (
		.D0(A), .D1(B), .S0(S),
		.Y(Y)
	);

endmodule
*/
