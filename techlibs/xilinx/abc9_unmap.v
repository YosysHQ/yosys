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

(* techmap_celltype = "$__ABC9_ASYNC0 $__ABC9_ASYNC1" *)
module $__ABC9_ASYNC01(input A, S, output Y);
  assign Y = A;
endmodule

module $__ABC9_FF_(input D, output Q);
  assign Q = D;
endmodule

module $__ABC9_RAM6(input A, input [5:0] S, output Y);
  assign Y = A;
endmodule
module $__ABC9_RAM7(input A, input [6:0] S, output Y);
  assign Y = A;
endmodule

module $__ABC9_DSP48E1(
    input [29:0] $A,
    input [17:0] $B,
    input [47:0] $C,
    input [24:0] $D,
    input [47:0] $P,
    input [47:0] $PCIN,
    input [47:0] $PCOUT,
    output [47:0] P,
    output [47:0] PCOUT
);
    parameter integer ADREG = 1;
    parameter integer AREG = 1;
    parameter integer BREG = 1;
    parameter integer CREG = 1;
    parameter integer DREG = 1;
    parameter integer MREG = 1;
    parameter integer PREG = 1;
    parameter USE_DPORT = "FALSE";
    parameter USE_MULT = "MULTIPLY";

    assign P = $P, PCOUT = $PCOUT;
endmodule
