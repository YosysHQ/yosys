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

module RAM32X1D (
  output DPO, SPO,
  input  D,
  input  WCLK,
  input  WE,
  input  A0, A1, A2, A3, A4,
  input  DPRA0, DPRA1, DPRA2, DPRA3, DPRA4
);
  parameter INIT = 32'h0;
  parameter IS_WCLK_INVERTED = 1'b0;
  wire \$DPO , \$SPO ;
  RAM32X1D #(
    .INIT(INIT), .IS_WCLK_INVERTED(IS_WCLK_INVERTED)
  ) _TECHMAP_REPLACE_ (
    .DPO(\$DPO ), .SPO(\$SPO ),
    .D(D), .WCLK(WCLK), .WE(WE),
    .A0(A0), .A1(A1), .A2(A2), .A3(A3), .A4(A4),
    .DPRA0(DPRA0), .DPRA1(DPRA1), .DPRA2(DPRA2), .DPRA3(DPRA3), .DPRA4(DPRA4)
  );
  \$__ABC_LUT6 dpo (.A(\$DPO ), .S({1'b0, A0, A1, A2, A3, A4}), .Y(DPO));
  \$__ABC_LUT6 spo (.A(\$SPO ), .S({1'b0, A0, A1, A2, A3, A4}), .Y(SPO));
endmodule

module RAM64X1D (
  output DPO, SPO,
  input  D,
  input  WCLK,
  input  WE,
  input  A0, A1, A2, A3, A4, A5,
  input  DPRA0, DPRA1, DPRA2, DPRA3, DPRA4, DPRA5
);
  parameter INIT = 64'h0;
  parameter IS_WCLK_INVERTED = 1'b0;
  wire \$DPO , \$SPO ;
  RAM64X1D #(
    .INIT(INIT), .IS_WCLK_INVERTED(IS_WCLK_INVERTED)
  ) _TECHMAP_REPLACE_ (
    .DPO(\$DPO ), .SPO(\$SPO ),
    .D(D), .WCLK(WCLK), .WE(WE),
    .A0(A0), .A1(A1), .A2(A2), .A3(A3), .A4(A4), .A5(A5),
    .DPRA0(DPRA0), .DPRA1(DPRA1), .DPRA2(DPRA2), .DPRA3(DPRA3), .DPRA4(DPRA4), .DPRA5(DPRA5)
  );
  \$__ABC_LUT6 dpo (.A(\$DPO ), .S({A0, A1, A2, A3, A4, A5}), .Y(DPO));
  \$__ABC_LUT6 spo (.A(\$SPO ), .S({A0, A1, A2, A3, A4, A5}), .Y(SPO));
endmodule

module RAM128X1D (
  output       DPO, SPO,
  input        D,
  input        WCLK,
  input        WE,
  input  [6:0] A, DPRA
);
  parameter INIT = 128'h0;
  parameter IS_WCLK_INVERTED = 1'b0;
  wire \$DPO , \$SPO ;
  RAM128X1D #(
    .INIT(INIT), .IS_WCLK_INVERTED(IS_WCLK_INVERTED)
  ) _TECHMAP_REPLACE_ (
    .DPO(\$DPO ), .SPO(\$SPO ),
    .D(D), .WCLK(WCLK), .WE(WE),
    .A(A),
    .DPRA(DPRA)
  );
  \$__ABC_LUT7 dpo (.A(\$DPO ), .S(A), .Y(DPO));
  \$__ABC_LUT7 spo (.A(\$SPO ), .S(A), .Y(SPO));
endmodule

module SRL16E (
  output Q,
  input A0, A1, A2, A3, CE, CLK, D
);
  parameter [15:0] INIT = 16'h0000;
  parameter [0:0] IS_CLK_INVERTED = 1'b0;
  wire \$Q ;
  SRL16E #(
    .INIT(INIT), .IS_CLK_INVERTED(IS_CLK_INVERTED)
  ) _TECHMAP_REPLACE_ (
    .Q(\$Q ),
    .A0(A0), .A1(A1), .A2(A2), .A3(A3), .CE(CE), .CLK(CLK), .D(D)
  );
  \$__ABC_LUT6 q (.A(\$Q ), .S({1'b1, A0, A1, A2, A3, 1'b1}), .Y(Q));
endmodule

module SRLC32E (
  output Q,
  output Q31,
  input [4:0] A,
  input CE, CLK, D
);
  parameter [31:0] INIT = 32'h00000000;
  parameter [0:0] IS_CLK_INVERTED = 1'b0;
  wire \$Q ;
  SRLC32E #(
    .INIT(INIT), .IS_CLK_INVERTED(IS_CLK_INVERTED)
  ) _TECHMAP_REPLACE_ (
    .Q(\$Q ), .Q31(Q31),
    .A(A), .CE(CE), .CLK(CLK), .D(D)
  );
  \$__ABC_LUT6 q (.A(\$Q ), .S({1'b1, A}), .Y(Q));
endmodule

module DSP48E1 (
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

    parameter _TECHMAP_CELLTYPE_ = "";
    localparam techmap_guard = (_TECHMAP_CELLTYPE_ != "");

    generate
    if (USE_MULT == "MULTIPLY" && USE_DPORT == "FALSE") begin
        wire [29:0] iA;
        wire [17:0] iB;
        wire [47:0] iC;
        wire [24:0] iD;

        wire pA, pB, pC, pD, pAD, pM, pP;
        wire [47:0] oP, oPCOUT;

		// Disconnect the A-input if MREG is enabled, since
		//   combinatorial path is broken
        if (AREG == 0 && MREG == 0 && PREG == 0)
            assign iA = A;
        else
            \$__ABC_DSP48E1_REG rA (.I(A), .O(iA), .Q(pA));
        if (BREG == 0 && MREG == 0 && PREG == 0)
            assign iB = B;
        else
            \$__ABC_DSP48E1_REG rB (.I(B), .O(iB), .Q(pB));
        if (CREG == 0 && PREG == 0)
            assign iC = C;
        else
            \$__ABC_DSP48E1_REG rC (.I(C), .O(iC), .Q(pC));
        if (DREG == 0)
            assign iD = D;
        else if (techmap_guard)
			$error("Invalid DSP48E1 configuration: DREG enabled but USE_DPORT == \"FALSE\"");
        if (ADREG == 1 && techmap_guard)
			$error("Invalid DSP48E1 configuration: ADREG enabled but USE_DPORT == \"FALSE\"");
		if (PREG == 0) begin
			if (MREG == 1)
				\$__ABC_DSP48E1_REG rM (.Q(pM));
		end
		else
            \$__ABC_DSP48E1_REG rP (.Q(pP));

        \$__ABC_DSP48E1_MULT_P_MUX muxP (
            .Aq(pA), .Bq(pB), .Cq(pC), .Dq(pD), .ADq(pAD), .Mq(pM), .P(oP), .Pq(pP), .O(P)
        );
        \$__ABC_DSP48E1_MULT_PCOUT_MUX muxPCOUT (
            .Aq(pA), .Bq(pB), .Cq(pC), .Dq(pD), .ADq(pAD), .Mq(pM), .P(oPCOUT), .Pq(pP), .O(PCOUT)
        );

        \$__ABC_DSP48E1_MULT #(
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
            .P(oP),
            .PATTERNBDETECT(PATTERNBDETECT),
            .PATTERNDETECT(PATTERNDETECT),
            .PCOUT(oPCOUT),
            .UNDERFLOW(UNDERFLOW),
            .A(iA),
            .ACIN(ACIN),
            .ALUMODE(ALUMODE),
            .B(iB),
            .BCIN(BCIN),
            .C(iC),
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
            .D(iD),
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
    end
    else if (USE_MULT == "MULTIPLY" && USE_DPORT == "TRUE") begin
        wire [29:0] iA;
        wire [17:0] iB;
        wire [47:0] iC;
        wire [24:0] iD;

        wire pA, pB, pC, pD, pAD, pM, pP;
        wire [47:0] oP, oPCOUT;

		// Disconnect the A-input if MREG is enabled, since
		//   combinatorial path is broken
        if (AREG == 0 && ADREG == 0 && MREG == 0 && PREG == 1)
            assign iA = A;
        else
            \$__ABC_DSP48E1_REG rA (.I(A), .O(iA), .Q(pA));
        if (BREG == 0 && MREG == 0 && PREG == 0)
            assign iB = B;
        else
            \$__ABC_DSP48E1_REG rB (.I(B), .O(iB), .Q(pB));
        if (CREG == 0 && PREG == 0)
            assign iC = C;
        else
            \$__ABC_DSP48E1_REG rC (.I(C), .O(iC), .Q(pC));
        if (DREG == 0 && ADREG == 0)
            assign iD = D;
        else
            \$__ABC_DSP48E1_REG rD (.I(D), .O(iD), .Q(pD));
		if (PREG == 0) begin
			if (MREG == 1)
				\$__ABC_DSP48E1_REG rM (.Q(pM));
            else if (ADREG == 1)
                \$__ABC_DSP48E1_REG rAD (.Q(pAD));
		end
		else
            \$__ABC_DSP48E1_REG rP (.Q(pP));

        \$__ABC_DSP48E1_MULT_DPORT_P_MUX muxP (
            .Aq(pA), .Bq(pB), .Cq(pC), .Dq(pD), .ADq(pAD), .Mq(pM), .P(oP), .Pq(pP), .O(P)
        );
        \$__ABC_DSP48E1_MULT_DPORT_PCOUT_MUX muxPCOUT (
            .Aq(pA), .Bq(pB), .Cq(pC), .Dq(pD), .ADq(pAD), .Mq(pM), .P(oPCOUT), .Pq(pP), .O(PCOUT)
        );

        \$__ABC_DSP48E1_MULT_DPORT #(
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
            .P(oP),
            .PATTERNBDETECT(PATTERNBDETECT),
            .PATTERNDETECT(PATTERNDETECT),
            .PCOUT(oPCOUT),
            .UNDERFLOW(UNDERFLOW),
            .A(iA),
            .ACIN(ACIN),
            .ALUMODE(ALUMODE),
            .B(iB),
            .BCIN(BCIN),
            .C(iC),
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
            .D(iD),
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
    end
    else
        $error("Invalid DSP48E1 configuration");
	endgenerate
endmodule
