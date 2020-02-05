/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *                2019  Eddie Hung    <eddie@fpgeh.com>
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

// Box containing MUXF7.[AB] + MUXF8,
//   Necessary to make these an atomic unit so that
//   ABC cannot optimise just one of the MUXF7 away
//   and expect to save on its delay
(* abc9_box_id = 3, lib_whitebox *)
module \$__XILINX_MUXF78 (output O, input I0, I1, I2, I3, S0, S1);
  assign O = S1 ? (S0 ? I3 : I2)
                : (S0 ? I1 : I0);
endmodule

module \$__ABC9_FF_ (input D, output Q);
endmodule

(* abc9_box_id = (9000+DELAY) *)
module \$__ABC9_DELAY (input I, output O);
  parameter DELAY = 0;
endmodule

// Box to emulate async behaviour of FDC*
(* abc9_box_id = 1000, lib_whitebox *)
module \$__ABC9_ASYNC0 (input A, S, output Y);
  assign Y = S ? 1'b0 : A;
endmodule

// Box to emulate async behaviour of FDP*
(* abc9_box_id = 1001, lib_whitebox *)
module \$__ABC9_ASYNC1 (input A, S, output Y);
  assign Y = S ? 1'b1 : A;
endmodule

// Box to emulate comb/seq behaviour of RAM{32,64} and SRL{16,32}
//   Necessary since RAMD* and SRL* have both combinatorial (i.e.
//   same-cycle read operation) and sequential (write operation
//   is only committed on the next clock edge).
//   To model the combinatorial path, such cells have to be split
//   into comb and seq parts, with this box modelling only the former.
(* abc9_box_id=2000 *)
module \$__ABC9_LUT6 (input A, input [5:0] S, output Y);
endmodule
// Box to emulate comb/seq behaviour of RAM128
(* abc9_box_id=2001 *)
module \$__ABC9_LUT7 (input A, input [6:0] S, output Y);
endmodule

// Boxes used to represent the comb behaviour of various modes
//   of DSP48E1
`define ABC9_DSP48E1(__NAME__) """
module __NAME__ (
    input [29:0] $A,
    input [17:0] $B,
    input [47:0] $C,
    input [24:0] $D,
    input [47:0] $P,
    input [47:0] $PCIN,
    input [47:0] $PCOUT,
    output [47:0] P,
    output [47:0] PCOUT);
endmodule
"""
(* abc9_box_id=3000 *) `ABC9_DSP48E1($__ABC9_DSP48E1_MULT)
(* abc9_box_id=3001 *) `ABC9_DSP48E1($__ABC9_DSP48E1_MULT_DPORT)
(* abc9_box_id=3002 *) `ABC9_DSP48E1($__ABC9_DSP48E1)
`undef ABC9_DSP48E1
