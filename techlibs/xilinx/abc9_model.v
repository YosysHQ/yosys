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

// Box to emulate comb/seq behaviour of RAMD{32,64} and SRL{16,32}
//   Necessary since RAMD* and SRL* have both combinatorial (i.e.
//   same-cycle read operation) and sequential (write operation
//   is only committed on the next clock edge).
//   To model the combinatorial path, such cells have to be split
//   into comb and seq parts, with this box modelling only the former.
(* abc9_box_id=2000 *)
module \$__ABC9_LUT6 (input A, input [5:0] S, output Y);
endmodule
// Box to emulate comb/seq behaviour of RAMD128
(* abc9_box_id=2001 *)
module \$__ABC9_LUT7 (input A, input [6:0] S, output Y);
endmodule


// Modules used to model the comb/seq behaviour of DSP48E1
//   With abc9_map.v responsible for splicing the below modules
//   between the combinatorial DSP48E1 box (e.g. disconnecting
//   A when AREG, MREG or PREG is enabled and splicing in the
//   "$__ABC9_DSP48E1_REG" blackbox as "REG" in the diagram below)
//   this acts to first disables the combinatorial path (as there
//   is no connectivity through REG), and secondly, since this is
//   blackbox a new PI will be introduced with an arrival time of
//   zero.
//   Note: Since these "$__ABC9_DSP48E1_REG" modules are of a
//   sequential nature, they are not passed as a box to ABC and
//   (desirably) represented as PO/PIs.
//
//   At the DSP output, we place a blackbox mux ("M" in the diagram
//   below) to capture the fact that the critical-path could come
//   from any one of its inputs.
//   In contrast to "REG", the "$__ABC9_DSP48E1_*_MUX" modules are
//   combinatorial blackboxes that do get passed to ABC.
//   The propagation delay through this box (specified in the box
//   file) captures the arrival time of the register (i.e.
//   propagation from AREG to P after clock edge), or zero delay
//   for the combinatorial path from the DSP.
//
//   Doing so should means that ABC is able to analyse the
//   worst-case delay through to P, regardless of if it was
//   through any combinatorial paths (e.g. B, below) or an
//   internal register (A2REG).
//   However, the true value of being as complete as this is
//   questionable since if AREG=1 and BREG=0 (as below)
//   then the worse-case path would very likely be through B
//   and very unlikely to be through AREG.Q...?
//
//   In graphical form:
//
//                 +-----+
//         +------>> REG >>----+
//         |       +-----+     |
//         |                   |
//         |    +---------+    |   __
//    A >>-+X X-|         |    +--|  \
//              | DSP48E1 |P      | M |--->> P
//              | AREG=1  |-------|__/
//    B >>------|         |
//              +---------+
//
`define ABC9_DSP48E1_MUX(__NAME__) """
module __NAME__ (input Aq, ADq, Bq, Cq, Dq, input [47:0] I, input Mq, input [47:0] P, input Pq, output [47:0] O);
endmodule
"""
(* abc9_box_id=2100 *) `ABC9_DSP48E1_MUX(\$__ABC9_DSP48E1_MULT_P_MUX )
(* abc9_box_id=2101 *) `ABC9_DSP48E1_MUX(\$__ABC9_DSP48E1_MULT_PCOUT_MUX )
(* abc9_box_id=2102 *) `ABC9_DSP48E1_MUX(\$__ABC9_DSP48E1_MULT_DPORT_P_MUX )
(* abc9_box_id=2103 *) `ABC9_DSP48E1_MUX(\$__ABC9_DSP48E1_MULT_DPORT_PCOUT_MUX )
(* abc9_box_id=2104 *) `ABC9_DSP48E1_MUX(\$__ABC9_DSP48E1_P_MUX )
(* abc9_box_id=2105 *) `ABC9_DSP48E1_MUX(\$__ABC9_DSP48E1_PCOUT_MUX )

`define ABC9_DSP48E1(__NAME__) """
module __NAME__ (
    output [29:0] ACOUT,
    output [17:0] BCOUT,
    output reg CARRYCASCOUT,
    output reg [3:0] CARRYOUT,
    output reg MULTSIGNOUT,
    output OVERFLOW,
    output reg signed [47:0] P,
    output PATTERNBDETECT,
    output PATTERNDETECT,
    output [47:0] PCOUT,
    output UNDERFLOW,
    input signed [29:0] A,
    input [29:0] ACIN,
    input [3:0] ALUMODE,
    input signed [17:0] B,
    input [17:0] BCIN,
    input [47:0] C,
    input CARRYCASCIN,
    input CARRYIN,
    input [2:0] CARRYINSEL,
    input CEA1,
    input CEA2,
    input CEAD,
    input CEALUMODE,
    input CEB1,
    input CEB2,
    input CEC,
    input CECARRYIN,
    input CECTRL,
    input CED,
    input CEINMODE,
    input CEM,
    input CEP,
    input CLK,
    input [24:0] D,
    input [4:0] INMODE,
    input MULTSIGNIN,
    input [6:0] OPMODE,
    input [47:0] PCIN,
    input RSTA,
    input RSTALLCARRYIN,
    input RSTALUMODE,
    input RSTB,
    input RSTC,
    input RSTCTRL,
    input RSTD,
    input RSTINMODE,
    input RSTM,
    input RSTP
);
    parameter integer ACASCREG = 1;
    parameter integer ADREG = 1;
    parameter integer ALUMODEREG = 1;
    parameter integer AREG = 1;
    parameter AUTORESET_PATDET = "NO_RESET";
    parameter A_INPUT = "DIRECT";
    parameter integer BCASCREG = 1;
    parameter integer BREG = 1;
    parameter B_INPUT = "DIRECT";
    parameter integer CARRYINREG = 1;
    parameter integer CARRYINSELREG = 1;
    parameter integer CREG = 1;
    parameter integer DREG = 1;
    parameter integer INMODEREG = 1;
    parameter integer MREG = 1;
    parameter integer OPMODEREG = 1;
    parameter integer PREG = 1;
    parameter SEL_MASK = "MASK";
    parameter SEL_PATTERN = "PATTERN";
    parameter USE_DPORT = "FALSE";
    parameter USE_MULT = "MULTIPLY";
    parameter USE_PATTERN_DETECT = "NO_PATDET";
    parameter USE_SIMD = "ONE48";
    parameter [47:0] MASK = 48'h3FFFFFFFFFFF;
    parameter [47:0] PATTERN = 48'h000000000000;
    parameter [3:0] IS_ALUMODE_INVERTED = 4'b0;
    parameter [0:0] IS_CARRYIN_INVERTED = 1'b0;
    parameter [0:0] IS_CLK_INVERTED = 1'b0;
    parameter [4:0] IS_INMODE_INVERTED = 5'b0;
    parameter [6:0] IS_OPMODE_INVERTED = 7'b0;
endmodule
"""
(* abc9_box_id=3000 *) `ABC9_DSP48E1(\$__ABC9_DSP48E1_MULT )
(* abc9_box_id=3001 *) `ABC9_DSP48E1(\$__ABC9_DSP48E1_MULT_DPORT )
(* abc9_box_id=3002 *) `ABC9_DSP48E1(\$__ABC9_DSP48E1 )
