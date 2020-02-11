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
(* abc9_box, lib_whitebox *)
module \$__XILINX_MUXF78 (output O, input I0, I1, I2, I3, S0, S1);
  assign O = S1 ? (S0 ? I3 : I2)
                : (S0 ? I1 : I0);
  specify
    (I0 => O) = 294;
    (I1 => O) = 297;
    (I2 => O) = 311;
    (I3 => O) = 317;
    (S0 => O) = 390;
    (S1 => O) = 273;
  endspecify
endmodule

module \$__ABC9_FF_ (input D, output Q);
endmodule

(* abc9_box *)
module \$__ABC9_DELAY (input I, output O);
  parameter DELAY = 0;
  specify
    (I => O) = DELAY;
  endspecify
endmodule

// Box to emulate async behaviour of FDC*
(* abc9_box, lib_whitebox *)
module \$__ABC9_ASYNC0 (input A, S, output Y);
  assign Y = S ? 1'b0 : A;
  specify
    (A => Y) = 0;
    (S => Y) = 764;
  endspecify
endmodule

// Box to emulate async behaviour of FDP*
(* abc9_box, lib_whitebox *)
module \$__ABC9_ASYNC1 (input A, S, output Y);
  assign Y = S ? 1'b1 : A;
  specify
    (A => Y) = 0;
    (S => Y) = 764;
  endspecify
endmodule

// Box to emulate comb/seq behaviour of RAM{32,64} and SRL{16,32}
//   Necessary since RAMD* and SRL* have both combinatorial (i.e.
//   same-cycle read operation) and sequential (write operation
//   is only committed on the next clock edge).
//   To model the combinatorial path, such cells have to be split
//   into comb and seq parts, with this box modelling only the former.
(* abc9_box *)
module \$__ABC9_LUT6 (input A, input [5:0] S, output Y);
  specify
    (S[0] => Y) = 642;
    (S[1] => Y) = 631;
    (S[2] => Y) = 472;
    (S[3] => Y) = 407;
    (S[4] => Y) = 238;
    (S[5] => Y) = 127;
  endspecify
endmodule
// Box to emulate comb/seq behaviour of RAM128
(* abc9_box *)
module \$__ABC9_LUT7 (input A, input [6:0] S, output Y);
  specify
    (S[0] => Y) = 1028;
    (S[1] => Y) = 1017;
    (S[2] => Y) =  858;
    (S[3] => Y) =  793;
    (S[4] => Y) =  624;
    (S[5] => Y) =  513;
    (S[6] => Y) =  464;
  endspecify
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
"""
(* abc9_box *) `ABC9_DSP48E1($__ABC9_DSP48E1_MULT)
  specify
    ($A *> P) = 2823;
    ($B *> P) = 2690;
    ($C *> P) = 1325;
    ($P *> P) = 0;
    ($A *> PCOUT) = 2970;
    ($B *> PCOUT) = 2838;
    ($C *> PCOUT) = 1474;
    ($PCOUT *> PCOUT) = 0;
  endspecify
endmodule
(* abc9_box *) `ABC9_DSP48E1($__ABC9_DSP48E1_MULT_DPORT)
  specify
    ($A *> P) = 3806;
    ($B *> P) = 2690;
    ($C *> P) = 1325;
    ($D *> P) = 3700;
    ($P *> P) = 0;
    ($A *> PCOUT) = 3954;
    ($B *> PCOUT) = 2838;
    ($C *> PCOUT) = 1474;
    ($D *> PCOUT) = 3700;
    ($PCOUT *> PCOUT) = 0;
  endspecify
endmodule
(* abc9_box *) `ABC9_DSP48E1($__ABC9_DSP48E1)
  specify
    ($A *> P) = 1523;
    ($B *> P) = 1509;
    ($C *> P) = 1325;
    ($P *> P) = 0;
    ($A *> PCOUT) = 1671;
    ($B *> PCOUT) = 1658;
    ($C *> PCOUT) = 1474;
    ($PCOUT *> PCOUT) = 0;
  endspecify
endmodule
`undef ABC9_DSP48E1
