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

module \$__ABC9_LUT6 (input A, input [5:0] S, output Y);
  assign Y = A;
endmodule
module \$__ABC9_LUT7 (input A, input [6:0] S, output Y);
  assign Y = A;
endmodule

module \$__ABC9_REG (input [WIDTH-1:0] I, output [WIDTH-1:0] O, output Q);
  parameter WIDTH = 1;
  assign O = I;
endmodule
(* techmap_celltype = "$__ABC9_DSP48E1_MULT_P_MUX $__ABC9_DSP48E1_MULT_PCOUT_MUX $__ABC9_DSP48E1_MULT_DPORT_P_MUX $__ABC9_DSP48E1_MULT_DPORT_PCOUT_MUX $__ABC9_DSP48E1_P_MUX $__ABC9_DSP48E1_PCOUT_MUX" *)
module \$__ABC9_DSP48E1_MUX (
  input Aq, Bq, Cq, Dq, ADq,
  input [47:0] I,
  input Mq,
  input [47:0] P, 
  input Pq, 
  output [47:0] O
);
  assign O = I;
endmodule

(* techmap_celltype = "$__ABC9_DSP48E1_MULT $__ABC9_DSP48E1_MULT_DPORT $__ABC9_DSP48E1" *)
module \$__ABC9_DSP48E1 (
    (* techmap_autopurge *) output [29:0] ACOUT,
    (* techmap_autopurge *) output [17:0] BCOUT,
    (* techmap_autopurge *) output reg CARRYCASCOUT,
    (* techmap_autopurge *) output reg [3:0] CARRYOUT,
    (* techmap_autopurge *) output reg MULTSIGNOUT,
    (* techmap_autopurge *) output OVERFLOW,
    (* techmap_autopurge *) output reg signed [47:0] P,
    (* techmap_autopurge *) output PATTERNBDETECT,
    (* techmap_autopurge *) output PATTERNDETECT,
    (* techmap_autopurge *) output [47:0] PCOUT,
    (* techmap_autopurge *) output UNDERFLOW,
    (* techmap_autopurge *) input signed [29:0] A,
    (* techmap_autopurge *) input [29:0] ACIN,
    (* techmap_autopurge *) input [3:0] ALUMODE,
    (* techmap_autopurge *) input signed [17:0] B,
    (* techmap_autopurge *) input [17:0] BCIN,
    (* techmap_autopurge *) input [47:0] C,
    (* techmap_autopurge *) input CARRYCASCIN,
    (* techmap_autopurge *) input CARRYIN,
    (* techmap_autopurge *) input [2:0] CARRYINSEL,
    (* techmap_autopurge *) input CEA1,
    (* techmap_autopurge *) input CEA2,
    (* techmap_autopurge *) input CEAD,
    (* techmap_autopurge *) input CEALUMODE,
    (* techmap_autopurge *) input CEB1,
    (* techmap_autopurge *) input CEB2,
    (* techmap_autopurge *) input CEC,
    (* techmap_autopurge *) input CECARRYIN,
    (* techmap_autopurge *) input CECTRL,
    (* techmap_autopurge *) input CED,
    (* techmap_autopurge *) input CEINMODE,
    (* techmap_autopurge *) input CEM,
    (* techmap_autopurge *) input CEP,
    (* techmap_autopurge *) input CLK,
    (* techmap_autopurge *) input [24:0] D,
    (* techmap_autopurge *) input [4:0] INMODE,
    (* techmap_autopurge *) input MULTSIGNIN,
    (* techmap_autopurge *) input [6:0] OPMODE,
    (* techmap_autopurge *) input [47:0] PCIN,
    (* techmap_autopurge *) input RSTA,
    (* techmap_autopurge *) input RSTALLCARRYIN,
    (* techmap_autopurge *) input RSTALUMODE,
    (* techmap_autopurge *) input RSTB,
    (* techmap_autopurge *) input RSTC,
    (* techmap_autopurge *) input RSTCTRL,
    (* techmap_autopurge *) input RSTD,
    (* techmap_autopurge *) input RSTINMODE,
    (* techmap_autopurge *) input RSTM,
    (* techmap_autopurge *) input RSTP
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

    DSP48E1 #(
        .ACASCREG(ACASCREG),
        .ADREG(ADREG),
        .ALUMODEREG(ALUMODEREG),
        .AREG(AREG),
        .AUTORESET_PATDET(AUTORESET_PATDET),
        .A_INPUT(A_INPUT),
        .BCASCREG(BCASCREG),
        .BREG(BREG),
        .B_INPUT(B_INPUT),
        .CARRYINREG(CARRYINREG),
        .CARRYINSELREG(CARRYINSELREG),
        .CREG(CREG),
        .DREG(DREG),
        .INMODEREG(INMODEREG),
        .MREG(MREG),
        .OPMODEREG(OPMODEREG),
        .PREG(PREG),
        .SEL_MASK(SEL_MASK),
        .SEL_PATTERN(SEL_PATTERN),
        .USE_DPORT(USE_DPORT),
        .USE_MULT(USE_MULT),
        .USE_PATTERN_DETECT(USE_PATTERN_DETECT),
        .USE_SIMD(USE_SIMD),
        .MASK(MASK),
        .PATTERN(PATTERN),
        .IS_ALUMODE_INVERTED(IS_ALUMODE_INVERTED),
        .IS_CARRYIN_INVERTED(IS_CARRYIN_INVERTED),
        .IS_CLK_INVERTED(IS_CLK_INVERTED),
        .IS_INMODE_INVERTED(IS_INMODE_INVERTED),
        .IS_OPMODE_INVERTED(IS_OPMODE_INVERTED)
    ) _TECHMAP_REPLACE_ (
        .ACOUT(ACOUT),
        .BCOUT(BCOUT),
        .CARRYCASCOUT(CARRYCASCOUT),
        .CARRYOUT(CARRYOUT),
        .MULTSIGNOUT(MULTSIGNOUT),
        .OVERFLOW(OVERFLOW),
        .P(P),
        .PATTERNBDETECT(PATTERNBDETECT),
        .PATTERNDETECT(PATTERNDETECT),
        .PCOUT(PCOUT),
        .UNDERFLOW(UNDERFLOW),
        .A(A),
        .ACIN(ACIN),
        .ALUMODE(ALUMODE),
        .B(B),
        .BCIN(BCIN),
        .C(C),
        .CARRYCASCIN(CARRYCASCIN),
        .CARRYIN(CARRYIN),
        .CARRYINSEL(CARRYINSEL),
        .CEA1(CEA1),
        .CEA2(CEA2),
        .CEAD(CEAD),
        .CEALUMODE(CEALUMODE),
        .CEB1(CEB1),
        .CEB2(CEB2),
        .CEC(CEC),
        .CECARRYIN(CECARRYIN),
        .CECTRL(CECTRL),
        .CED(CED),
        .CEINMODE(CEINMODE),
        .CEM(CEM),
        .CEP(CEP),
        .CLK(CLK),
        .D(D),
        .INMODE(INMODE),
        .MULTSIGNIN(MULTSIGNIN),
        .OPMODE(OPMODE),
        .PCIN(PCIN),
        .RSTA(RSTA),
        .RSTALLCARRYIN(RSTALLCARRYIN),
        .RSTALUMODE(RSTALUMODE),
        .RSTB(RSTB),
        .RSTC(RSTC),
        .RSTCTRL(RSTCTRL),
        .RSTD(RSTD),
        .RSTINMODE(RSTINMODE),
        .RSTM(RSTM),
        .RSTP(RSTP)
    );
endmodule
