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

module \$lut (A, Y);
	parameter WIDTH = 0;
	parameter LUT = 0;

	(* force_downto *)
	input [WIDTH-1:0] A;
	output Y;

	generate
		if (WIDTH == 1) begin
			CC_LUT1 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.O(Y), .I0(A[0]));
		end
		else if (WIDTH == 2) begin
			CC_LUT2 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.O(Y), .I0(A[0]), .I1(A[1]));
		end
		else if (WIDTH == 3) begin
			CC_LUT3 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.O(Y), .I0(A[0]), .I1(A[1]), .I2(A[2]));
		end
		else if (WIDTH == 4) begin
			CC_LUT4 #(.INIT(LUT)) _TECHMAP_REPLACE_ (.O(Y), .I0(A[0]), .I1(A[1]), .I2(A[2]), .I3(A[3]));
		end
		else begin
			wire _TECHMAP_FAIL_ = 1;
		end
	endgenerate
endmodule
