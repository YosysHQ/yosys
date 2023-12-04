// Copyright 2020-2022 F4PGA Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0

// DFF, asynchronous set/reset, enable
module \$_DFFSRE_PNNP_ (C, S, R, E, D, Q);
	input  C;
	input  S;
	input  R;
	input  E;
	input  D;
	output Q;
	dffsre _TECHMAP_REPLACE_ (.Q(Q), .D(D), .C(C), .E(E), .R(R), .S(S));
endmodule

module \$_DFFSRE_NNNP_ (C, S, R, E, D, Q);
	input  C;
	input  S;
	input  R;
	input  E;
	input  D;
	output Q;
	dffnsre _TECHMAP_REPLACE_ (.Q(Q), .D(D), .C(C), .E(E), .R(R), .S(S));
endmodule

// DFF, synchronous set or reset, enable
module \$_SDFFE_PN0P_ (D, C, R, E, Q);
	input  D;
	input  C;
	input  R;
	input  E;
	output Q;
	sdffsre _TECHMAP_REPLACE_ (.Q(Q), .D(D), .C(C), .E(E), .R(R), .S(1'b1));
endmodule

module \$_SDFFE_PN1P_ (D, C, R, E, Q);
	input  D;
	input  C;
	input  R;
	input  E;
	output Q;
	sdffsre _TECHMAP_REPLACE_ (.Q(Q), .D(D), .C(C), .E(E), .R(1'b1), .S(R));
endmodule

module \$_SDFFE_NN0P_ (D, C, R, E, Q);
	input  D;
	input  C;
	input  R;
	input  E;
	output Q;
	sdffnsre _TECHMAP_REPLACE_ (.Q(Q), .D(D), .C(C), .E(E), .R(R), .S(1'b1));
endmodule

module \$_SDFFE_NN1P_ (D, C, R, E, Q);
	input  D;
	input  C;
	input  R;
	input  E;
	output Q;
	sdffnsre _TECHMAP_REPLACE_ (.Q(Q), .D(D), .C(C), .E(E), .R(1'b1), .S(R));
endmodule

// Latch, no set/reset, no enable
module  \$_DLATCH_P_ (input E, D, output Q);
	latchsre  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .E(1'b1), .G(E), .R(1'b1), .S(1'b1));
endmodule

module  \$_DLATCH_N_ (input E, D, output Q);
	latchnsre _TECHMAP_REPLACE_ (.D(D), .Q(Q), .E(1'b1), .G(E), .R(1'b1), .S(1'b1));
endmodule

// Latch with async set and reset and enable
module  \$_DLATCHSR_PPP_ (input E, S, R, D, output Q);
	latchsre  _TECHMAP_REPLACE_ (.D(D), .Q(Q), .E(1'b1), .G(E),  .R(!R), .S(!S));
endmodule

module  \$_DLATCHSR_NPP_ (input E, S, R, D, output Q);
	latchnsre _TECHMAP_REPLACE_ (.D(D), .Q(Q), .E(1'b1), .G(E),  .R(!R), .S(!S));
endmodule

module \$__SHREG_DFF_P_ (D, Q, C);
	input  D;
	input  C;
	output Q;

	parameter DEPTH = 2;

	reg [DEPTH-2:0] q;

	genvar i;
	generate for (i = 0; i < DEPTH; i = i + 1) begin: slice

		// First in chain
		generate if (i == 0) begin
				 sh_dff #() shreg_beg (
					.Q(q[i]),
					.D(D),
					.C(C)
				);
		end endgenerate
		// Middle in chain
		generate if (i > 0 && i != DEPTH-1) begin
				 sh_dff #() shreg_mid (
					.Q(q[i]),
					.D(q[i-1]),
					.C(C)
				);
		end endgenerate
		// Last in chain
		generate if (i == DEPTH-1) begin
				 sh_dff #() shreg_end (
					.Q(Q),
					.D(q[i-1]),
					.C(C)
				);
		end endgenerate
   end: slice
   endgenerate

endmodule

