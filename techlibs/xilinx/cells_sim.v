/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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

// See Xilinx UG953 and UG474 for a description of the cell types below.
// http://www.xilinx.com/support/documentation/user_guides/ug474_7Series_CLB.pdf
// http://www.xilinx.com/support/documentation/sw_manuals/xilinx2014_4/ug953-vivado-7series-libraries.pdf

module VCC(output P);
  assign P = 1;
endmodule

module GND(output G);
  assign G = 0;
endmodule

module IBUF(output O, input I);
  parameter IOSTANDARD = "default";
  parameter IBUF_LOW_PWR = 0;
  assign O = I;
endmodule

module OBUF(output O, input I);
  parameter IOSTANDARD = "default";
  parameter DRIVE = 12;
  parameter SLEW = "SLOW";
  assign O = I;
endmodule

module BUFG(output O, input I);
  assign O = I;
endmodule

module BUFGCTRL(
    output O,
    input I0, input I1,
    input S0, input S1,
    input CE0, input CE1,
    input IGNORE0, input IGNORE1);

parameter [0:0] INIT_OUT = 1'b0;
parameter PRESELECT_I0 = "FALSE";
parameter PRESELECT_I1 = "FALSE";
parameter [0:0] IS_CE0_INVERTED = 1'b0;
parameter [0:0] IS_CE1_INVERTED = 1'b0;
parameter [0:0] IS_S0_INVERTED = 1'b0;
parameter [0:0] IS_S1_INVERTED = 1'b0;
parameter [0:0] IS_IGNORE0_INVERTED = 1'b0;
parameter [0:0] IS_IGNORE1_INVERTED = 1'b0;

wire I0_internal = ((CE0 ^ IS_CE0_INVERTED) ? I0 : INIT_OUT);
wire I1_internal = ((CE1 ^ IS_CE1_INVERTED) ? I1 : INIT_OUT);
wire S0_true = (S0 ^ IS_S0_INVERTED);
wire S1_true = (S1 ^ IS_S1_INVERTED);

assign O = S0_true ? I0_internal : (S1_true ? I1_internal : INIT_OUT);

endmodule

module BUFHCE(output O, input I, input CE);

parameter [0:0] INIT_OUT = 1'b0;
parameter CE_TYPE = "SYNC";
parameter [0:0] IS_CE_INVERTED = 1'b0;

assign O = ((CE ^ IS_CE_INVERTED) ? I : INIT_OUT);

endmodule

// module OBUFT(output O, input I, T);
//   assign O = T ? 1'bz : I;
// endmodule

// module IOBUF(inout IO, output O, input I, T);
//   assign O = IO, IO = T ? 1'bz : I;
// endmodule

module INV(output O, input I);
  assign O = !I;
endmodule

module LUT1(output O, input I0);
  parameter [1:0] INIT = 0;
  assign O = I0 ? INIT[1] : INIT[0];
endmodule

module LUT2(output O, input I0, I1);
  parameter [3:0] INIT = 0;
  wire [ 1: 0] s1 = I1 ? INIT[ 3: 2] : INIT[ 1: 0];
  assign O = I0 ? s1[1] : s1[0];
endmodule

module LUT3(output O, input I0, I1, I2);
  parameter [7:0] INIT = 0;
  wire [ 3: 0] s2 = I2 ? INIT[ 7: 4] : INIT[ 3: 0];
  wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
  assign O = I0 ? s1[1] : s1[0];
endmodule

module LUT4(output O, input I0, I1, I2, I3);
  parameter [15:0] INIT = 0;
  wire [ 7: 0] s3 = I3 ? INIT[15: 8] : INIT[ 7: 0];
  wire [ 3: 0] s2 = I2 ?   s3[ 7: 4] :   s3[ 3: 0];
  wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
  assign O = I0 ? s1[1] : s1[0];
endmodule

module LUT5(output O, input I0, I1, I2, I3, I4);
  parameter [31:0] INIT = 0;
  wire [15: 0] s4 = I4 ? INIT[31:16] : INIT[15: 0];
  wire [ 7: 0] s3 = I3 ?   s4[15: 8] :   s4[ 7: 0];
  wire [ 3: 0] s2 = I2 ?   s3[ 7: 4] :   s3[ 3: 0];
  wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
  assign O = I0 ? s1[1] : s1[0];
endmodule

module LUT6(output O, input I0, I1, I2, I3, I4, I5);
  parameter [63:0] INIT = 0;
  wire [31: 0] s5 = I5 ? INIT[63:32] : INIT[31: 0];
  wire [15: 0] s4 = I4 ?   s5[31:16] :   s5[15: 0];
  wire [ 7: 0] s3 = I3 ?   s4[15: 8] :   s4[ 7: 0];
  wire [ 3: 0] s2 = I2 ?   s3[ 7: 4] :   s3[ 3: 0];
  wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
  assign O = I0 ? s1[1] : s1[0];
endmodule

module LUT6_2(output O6, output O5, input I0, I1, I2, I3, I4, I5);
  parameter [63:0] INIT = 0;
  wire [31: 0] s5 = I5 ? INIT[63:32] : INIT[31: 0];
  wire [15: 0] s4 = I4 ?   s5[31:16] :   s5[15: 0];
  wire [ 7: 0] s3 = I3 ?   s4[15: 8] :   s4[ 7: 0];
  wire [ 3: 0] s2 = I2 ?   s3[ 7: 4] :   s3[ 3: 0];
  wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
  assign O6 = I0 ? s1[1] : s1[0];

  wire [15: 0] s5_4 = I4 ? INIT[31:16] : INIT[15: 0];
  wire [ 7: 0] s5_3 = I3 ? s5_4[15: 8] : s5_4[ 7: 0];
  wire [ 3: 0] s5_2 = I2 ? s5_3[ 7: 4] : s5_3[ 3: 0];
  wire [ 1: 0] s5_1 = I1 ? s5_2[ 3: 2] : s5_2[ 1: 0];
  assign O5 = I0 ? s5_1[1] : s5_1[0];
endmodule

module MUXCY(output O, input CI, DI, S);
  assign O = S ? CI : DI;
endmodule

(* abc_box_id = 1, lib_whitebox *)
module MUXF7(output O, input I0, I1, S);
  assign O = S ? I1 : I0;
endmodule

(* abc_box_id = 2, lib_whitebox *)
module MUXF8(output O, input I0, I1, S);
  assign O = S ? I1 : I0;
endmodule

`ifdef _ABC
(* abc_box_id = 3, lib_whitebox *)
module \$__XILINX_MUXF78 (output O, input I0, I1, I2, I3, S0, S1);
  assign O = S1 ? (S0 ? I3 : I2)
                : (S0 ? I1 : I0);
endmodule
`endif

module XORCY(output O, input CI, LI);
  assign O = CI ^ LI;
endmodule

(* abc_box_id = 4, abc_carry="CI,CO", lib_whitebox *)
module CARRY4(output [3:0] CO, O, input CI, CYINIT, input [3:0] DI, S);
  assign O = S ^ {CO[2:0], CI | CYINIT};
  assign CO[0] = S[0] ? CI | CYINIT : DI[0];
  assign CO[1] = S[1] ? CO[0] : DI[1];
  assign CO[2] = S[2] ? CO[1] : DI[2];
  assign CO[3] = S[3] ? CO[2] : DI[3];
endmodule

`ifdef _EXPLICIT_CARRY

module CARRY0(output CO_CHAIN, CO_FABRIC, O, input CI, CI_INIT, DI, S);
  parameter CYINIT_FABRIC = 0;
  wire CI_COMBINE;
  if(CYINIT_FABRIC) begin
    assign CI_COMBINE = CI_INIT;
  end else begin
    assign CI_COMBINE = CI;
  end
  assign CO_CHAIN = S ? CI_COMBINE : DI;
  assign CO_FABRIC = S ? CI_COMBINE : DI;
  assign O = S ^ CI_COMBINE;
endmodule

module CARRY(output CO_CHAIN, CO_FABRIC, O, input CI, DI, S);
  assign CO_CHAIN = S ? CI : DI;
  assign CO_FABRIC = S ? CI : DI;
  assign O = S ^ CI;
endmodule

`endif

module FDRE (output reg Q, input C, CE, D, R);
  parameter [0:0] INIT = 1'b0;
  parameter [0:0] IS_C_INVERTED = 1'b0;
  parameter [0:0] IS_D_INVERTED = 1'b0;
  parameter [0:0] IS_R_INVERTED = 1'b0;
  initial Q <= INIT;
  generate case (|IS_C_INVERTED)
    1'b0: always @(posedge C) if (R == !IS_R_INVERTED) Q <= 1'b0; else if (CE) Q <= D ^ IS_D_INVERTED;
    1'b1: always @(negedge C) if (R == !IS_R_INVERTED) Q <= 1'b0; else if (CE) Q <= D ^ IS_D_INVERTED;
  endcase endgenerate
endmodule

module FDSE (output reg Q, input C, CE, D, S);
  parameter [0:0] INIT = 1'b1;
  parameter [0:0] IS_C_INVERTED = 1'b0;
  parameter [0:0] IS_D_INVERTED = 1'b0;
  parameter [0:0] IS_S_INVERTED = 1'b0;
  initial Q <= INIT;
  generate case (|IS_C_INVERTED)
    1'b0: always @(posedge C) if (S == !IS_S_INVERTED) Q <= 1'b1; else if (CE) Q <= D ^ IS_D_INVERTED;
    1'b1: always @(negedge C) if (S == !IS_S_INVERTED) Q <= 1'b1; else if (CE) Q <= D ^ IS_D_INVERTED;
  endcase endgenerate
endmodule

module FDCE (output reg Q, input C, CE, D, CLR);
  parameter [0:0] INIT = 1'b0;
  parameter [0:0] IS_C_INVERTED = 1'b0;
  parameter [0:0] IS_D_INVERTED = 1'b0;
  parameter [0:0] IS_CLR_INVERTED = 1'b0;
  initial Q <= INIT;
  generate case ({|IS_C_INVERTED, |IS_CLR_INVERTED})
    2'b00: always @(posedge C, posedge CLR) if ( CLR) Q <= 1'b0; else if (CE) Q <= D ^ IS_D_INVERTED;
    2'b01: always @(posedge C, negedge CLR) if (!CLR) Q <= 1'b0; else if (CE) Q <= D ^ IS_D_INVERTED;
    2'b10: always @(negedge C, posedge CLR) if ( CLR) Q <= 1'b0; else if (CE) Q <= D ^ IS_D_INVERTED;
    2'b11: always @(negedge C, negedge CLR) if (!CLR) Q <= 1'b0; else if (CE) Q <= D ^ IS_D_INVERTED;
  endcase endgenerate
endmodule

module FDPE (output reg Q, input C, CE, D, PRE);
  parameter [0:0] INIT = 1'b1;
  parameter [0:0] IS_C_INVERTED = 1'b0;
  parameter [0:0] IS_D_INVERTED = 1'b0;
  parameter [0:0] IS_PRE_INVERTED = 1'b0;
  initial Q <= INIT;
  generate case ({|IS_C_INVERTED, |IS_PRE_INVERTED})
    2'b00: always @(posedge C, posedge PRE) if ( PRE) Q <= 1'b1; else if (CE) Q <= D ^ IS_D_INVERTED;
    2'b01: always @(posedge C, negedge PRE) if (!PRE) Q <= 1'b1; else if (CE) Q <= D ^ IS_D_INVERTED;
    2'b10: always @(negedge C, posedge PRE) if ( PRE) Q <= 1'b1; else if (CE) Q <= D ^ IS_D_INVERTED;
    2'b11: always @(negedge C, negedge PRE) if (!PRE) Q <= 1'b1; else if (CE) Q <= D ^ IS_D_INVERTED;
  endcase endgenerate
endmodule

module FDRE_1 (output reg Q, input C, CE, D, R);
  parameter [0:0] INIT = 1'b0;
  initial Q <= INIT;
  always @(negedge C) if (R) Q <= 1'b0; else if(CE) Q <= D;
endmodule

module FDSE_1 (output reg Q, input C, CE, D, S);
  parameter [0:0] INIT = 1'b1;
  initial Q <= INIT;
  always @(negedge C) if (S) Q <= 1'b1; else if(CE) Q <= D;
endmodule

module FDCE_1 (output reg Q, input C, CE, D, CLR);
  parameter [0:0] INIT = 1'b0;
  initial Q <= INIT;
  always @(negedge C, posedge CLR) if (CLR) Q <= 1'b0; else if (CE) Q <= D;
endmodule

module FDPE_1 (output reg Q, input C, CE, D, PRE);
  parameter [0:0] INIT = 1'b1;
  initial Q <= INIT;
  always @(negedge C, posedge PRE) if (PRE) Q <= 1'b1; else if (CE) Q <= D;
endmodule

(* abc_box_id = 5, abc_scc_break="D,WE" *)
module RAM32X1D (
  output DPO, SPO,
  input  D, WCLK, WE,
  input  A0, A1, A2, A3, A4,
  input  DPRA0, DPRA1, DPRA2, DPRA3, DPRA4
);
  parameter INIT = 32'h0;
  parameter IS_WCLK_INVERTED = 1'b0;
  wire [4:0] a = {A4, A3, A2, A1, A0};
  wire [4:0] dpra = {DPRA4, DPRA3, DPRA2, DPRA1, DPRA0};
  reg [31:0] mem = INIT;
  assign SPO = mem[a];
  assign DPO = mem[dpra];
  wire clk = WCLK ^ IS_WCLK_INVERTED;
  always @(posedge clk) if (WE) mem[a] <= D;
endmodule

(* abc_box_id = 6, abc_scc_break="D,WE" *)
module RAM64X1D (
  output DPO, SPO,
  input  D, WCLK, WE,
  input  A0, A1, A2, A3, A4, A5,
  input  DPRA0, DPRA1, DPRA2, DPRA3, DPRA4, DPRA5
);
  parameter INIT = 64'h0;
  parameter IS_WCLK_INVERTED = 1'b0;
  wire [5:0] a = {A5, A4, A3, A2, A1, A0};
  wire [5:0] dpra = {DPRA5, DPRA4, DPRA3, DPRA2, DPRA1, DPRA0};
  reg [63:0] mem = INIT;
  assign SPO = mem[a];
  assign DPO = mem[dpra];
  wire clk = WCLK ^ IS_WCLK_INVERTED;
  always @(posedge clk) if (WE) mem[a] <= D;
endmodule

(* abc_box_id = 7, abc_scc_break="D,WE" *)
module RAM128X1D (
  output       DPO, SPO,
  input        D, WCLK, WE,
  input  [6:0] A, DPRA
);
  parameter INIT = 128'h0;
  parameter IS_WCLK_INVERTED = 1'b0;
  reg [127:0] mem = INIT;
  assign SPO = mem[A];
  assign DPO = mem[DPRA];
  wire clk = WCLK ^ IS_WCLK_INVERTED;
  always @(posedge clk) if (WE) mem[A] <= D;
endmodule

module SRL16E (
  output Q,
  input A0, A1, A2, A3, CE, CLK, D
);
  parameter [15:0] INIT = 16'h0000;
  parameter [0:0] IS_CLK_INVERTED = 1'b0;

  reg [15:0] r = INIT;
  assign Q = r[{A3,A2,A1,A0}];
  generate
    if (IS_CLK_INVERTED) begin
      always @(negedge CLK) if (CE) r <= { r[14:0], D };
    end
    else
        always @(posedge CLK) if (CE) r <= { r[14:0], D };
  endgenerate
endmodule

module SRLC32E (
  output Q,
  output Q31,
  input [4:0] A,
  input CE, CLK, D
);
  parameter [31:0] INIT = 32'h00000000;
  parameter [0:0] IS_CLK_INVERTED = 1'b0;

  reg [31:0] r = INIT;
  assign Q31 = r[31];
  assign Q = r[A];
  generate
    if (IS_CLK_INVERTED) begin
      always @(negedge CLK) if (CE) r <= { r[30:0], D };
    end
    else
      always @(posedge CLK) if (CE) r <= { r[30:0], D };
  endgenerate
endmodule

module DSP48E1 (
    output [29:0] ACOUT,
    output [17:0] BCOUT,
    output CARRYCASCOUT,
    output [3:0] CARRYOUT,
    output MULTSIGNOUT,
    output OVERFLOW,
    output reg [47:0] P,
    output PATTERNBDETECT,
    output PATTERNDETECT,
    output [47:0] PCOUT,
    output UNDERFLOW,
    input [29:0] A,
    input [29:0] ACIN,
    input [3:0] ALUMODE,
    input [17:0] B,
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

    initial begin
`ifdef __ICARUS__
        if (ACASCREG != 0)          $fatal(1, "Unsupported ACASCREG value");
        if (ADREG != 0)             $fatal(1, "Unsupported ADREG value");
        if (ALUMODEREG != 0)        $fatal(1, "Unsupported ALUMODEREG value");
        if (AREG != 0)              $fatal(1, "Unsupported AREG value");
        if (AUTORESET_PATDET != "NO_RESET") $fatal(1, "Unsupported AUTORESET_PATDET value");
        if (A_INPUT != "DIRECT")    $fatal(1, "Unsupported A_INPUT value");
        if (BCASCREG != 0)          $fatal(1, "Unsupported BCASCREG value");
        if (BREG != 0)              $fatal(1, "Unsupported BREG value");
        if (B_INPUT != "DIRECT")    $fatal(1, "Unsupported B_INPUT value");
        if (CARRYINREG != 0)        $fatal(1, "Unsupported CARRYINREG value");
        if (CARRYINSELREG != 0)     $fatal(1, "Unsupported CARRYINSELREG value");
        if (CREG != 0)              $fatal(1, "Unsupported CREG value");
        if (DREG != 0)              $fatal(1, "Unsupported DREG value");
        if (INMODEREG != 0)         $fatal(1, "Unsupported INMODEREG value");
        if (MREG != 0)              $fatal(1, "Unsupported MREG value");
        if (OPMODEREG != 0)         $fatal(1, "Unsupported OPMODEREG value");
        if (PREG != 0)              $fatal(1, "Unsupported PREG value");
        if (SEL_MASK != "MASK")     $fatal(1, "Unsupported SEL_MASK value");
        if (SEL_PATTERN != "PATTERN") $fatal(1, "Unsupported SEL_PATTERN value");
        if (USE_DPORT != "FALSE")   $fatal(1, "Unsupported USE_DPORT value");
        if (USE_MULT != "MULTIPLY") $fatal(1, "Unsupported USE_MULT value");
        if (USE_PATTERN_DETECT != "NO_PATDET") $fatal(1, "Unsupported USE_PATTERN_DETECT value");
        if (USE_SIMD != "ONE48")    $fatal(1, "Unsupported USE_SIMD value");
        if (IS_ALUMODE_INVERTED != 4'b0) $fatal(1, "Unsupported IS_ALUMODE_INVERTED value");
        if (IS_CARRYIN_INVERTED != 1'b0) $fatal(1, "Unsupported IS_CARRYIN_INVERTED value");
        if (IS_CLK_INVERTED != 1'b0) $fatal(1, "Unsupported IS_CLK_INVERTED value");
        if (IS_INMODE_INVERTED != 5'b0) $fatal(1, "Unsupported IS_INMODE_INVERTED value");
        if (IS_OPMODE_INVERTED != 7'b0) $fatal(1, "Unsupported IS_OPMODE_INVERTED value");
`endif
    end

    always @* begin
        P <= {48{1'bx}};
`ifdef __ICARUS__
        if (INMODE != 4'b0000)      $fatal(1, "Unsupported INMODE value");
        if (ALUMODE != 4'b0000)     $fatal(1, "Unsupported ALUMODE value");
        if (OPMODE != 7'b000101)    $fatal(1, "Unsupported OPMODE value");
        if (CARRYINSEL != 3'b000)   $fatal(1, "Unsupported CARRYINSEL value");
        if (ACIN != 30'b0)          $fatal(1, "Unsupported ACIN value");
        if (BCIN != 18'b0)          $fatal(1, "Unsupported BCIN value");
        if (PCIN != 48'b0)          $fatal(1, "Unsupported PCIN value");
        if (CARRYIN != 1'b0)        $fatal(1, "Unsupported CARRYIN value");
`endif
        P[42:0] <= A[24:0] * B;
    end
endmodule
