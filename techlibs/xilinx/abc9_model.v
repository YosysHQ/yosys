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

// Box to emulate async behaviour of FDC*
(* abc9_box, lib_whitebox *)
module \$__ABC9_ASYNC0 (input A, S, output Y);
  assign Y = S ? 1'b0 : A;
  specify
    (A => Y) = 0;
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L270
    (S => Y) = 764;
  endspecify
endmodule

// Box to emulate async behaviour of FDP*
(* abc9_box, lib_whitebox *)
module \$__ABC9_ASYNC1 (input A, S, output Y);
  assign Y = S ? 1'b1 : A;
  specify
    (A => Y) = 0;
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L270
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
module \$__ABC9_RAM6 (input A, input [5:0] S, output Y);
  specify
    (A    => Y) =   0;
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
module \$__ABC9_RAM7 (input A, input [6:0] S, output Y);
  specify
    (A    => Y) = 0;
                                                    // https://github.com/SymbiFlow/prjxray-db/blob/1c85daf1b115da4d27ca83c6b89f53a94de39748/artix7/timings/slicel.sdf#L867
    (S[0] => Y) = 642 + 223 /* to cross F7BMUX */ + 174 /* CMUX */;
    (S[1] => Y) = 631 + 223 /* to cross F7BMUX */ + 174 /* CMUX */;
    (S[2] => Y) = 472 + 223 /* to cross F7BMUX */ + 174 /* CMUX */;
    (S[3] => Y) = 407 + 223 /* to cross F7BMUX */ + 174 /* CMUX */;
    (S[4] => Y) = 238 + 223 /* to cross F7BMUX */ + 174 /* CMUX */;
    (S[5] => Y) = 127 + 223 /* to cross F7BMUX */ + 174 /* CMUX */;
    (S[6] => Y) = 0 + 296 /* to select F7BMUX */ + 174 /* CMUX */;
  endspecify
endmodule

// Boxes used to represent the comb behaviour of DSP48E1
(* abc9_box *)
module $__ABC9_DSP48E1 (
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

    function integer \A.P.comb ;
    begin
        if (USE_MULT == "MULTIPLY" && USE_DPORT == "FALSE")     \A.P.comb = 2823;
        else if (USE_MULT == "MULTIPLY" && USE_DPORT == "TRUE") \A.P.comb = 3806;
        else if (USE_MULT == "NONE" && USE_DPORT == "FALSE")    \A.P.comb = 1523;
    end
    endfunction
    function integer \A.PCOUT.comb ;
    begin
        if (USE_MULT == "MULTIPLY" && USE_DPORT == "FALSE")     \A.PCOUT.comb = 2970;
        else if (USE_MULT == "MULTIPLY" && USE_DPORT == "TRUE") \A.PCOUT.comb = 3954;
        else if (USE_MULT == "NONE" && USE_DPORT == "FALSE")    \A.PCOUT.comb = 1671;
    end
    endfunction
    function integer \B.P.comb ;
    begin
        if (USE_MULT == "MULTIPLY" && USE_DPORT == "FALSE")     \B.P.comb = 2690;
        else if (USE_MULT == "MULTIPLY" && USE_DPORT == "TRUE") \B.P.comb = 2690;
        else if (USE_MULT == "NONE" && USE_DPORT == "FALSE")    \B.P.comb = 1509;
    end
    endfunction
    function integer \B.PCOUT.comb ;
    begin
        if (USE_MULT == "MULTIPLY" && USE_DPORT == "FALSE")     \B.PCOUT.comb = 2838;
        else if (USE_MULT == "MULTIPLY" && USE_DPORT == "TRUE") \B.PCOUT.comb = 2838;
        else if (USE_MULT == "NONE" && USE_DPORT == "FALSE")    \B.PCOUT.comb = 1658;
    end
    endfunction
    function integer \C.P.comb ;
    begin
        if (USE_MULT == "MULTIPLY" && USE_DPORT == "FALSE")     \C.P.comb = 1325;
        else if (USE_MULT == "MULTIPLY" && USE_DPORT == "TRUE") \C.P.comb = 1325;
        else if (USE_MULT == "NONE" && USE_DPORT == "FALSE")    \C.P.comb = 1325;
    end
    endfunction
    function integer \C.PCOUT.comb ;
    begin
        if (USE_MULT == "MULTIPLY" && USE_DPORT == "FALSE")     \C.PCOUT.comb = 1474;
        else if (USE_MULT == "MULTIPLY" && USE_DPORT == "TRUE") \C.PCOUT.comb = 1474;
        else if (USE_MULT == "NONE" && USE_DPORT == "FALSE")    \C.PCOUT.comb = 1474;
    end
    endfunction
    function integer \D.P.comb ;
    begin
        if (USE_MULT == "MULTIPLY" && USE_DPORT == "TRUE")      \D.P.comb = 3717;
    end
    endfunction
    function integer \D.PCOUT.comb ;
    begin
        if (USE_MULT == "MULTIPLY" && USE_DPORT == "TRUE")      \D.PCOUT.comb = 3700;
    end
    endfunction

	specify
		($P *> P) 			= 0;
		($PCOUT *> PCOUT)	= 0;
	endspecify

    // Identical comb delays to DSP48E1 in cells_sim.v
    generate
        if (PREG == 0 && MREG == 0 && AREG == 0 && ADREG == 0)
            specify
                ($A *> P) =      \A.P.comb ();
                ($A *> PCOUT) =  \A.PCOUT.comb ();
            endspecify

        if (PREG == 0 && MREG == 0 && BREG == 0)
            specify
                ($B *> P) =      \B.P.comb ();
                ($B *> PCOUT) =  \B.PCOUT.comb ();
            endspecify

        if (PREG == 0 && CREG == 0)
            specify
                ($C *> P) =      \C.P.comb ();
                ($C *> PCOUT) =  \C.PCOUT.comb ();
            endspecify

        if (PREG == 0 && MREG == 0 && ADREG == 0 && DREG == 0)
            specify
                ($D *> P) =      \D.P.comb ();
                ($D *> PCOUT) =  \D.PCOUT.comb ();
            endspecify

        if (PREG == 0)
            specify
                ($PCIN *> P) =       1107;
                ($PCIN *> PCOUT) =   1255;
            endspecify
    endgenerate
endmodule
