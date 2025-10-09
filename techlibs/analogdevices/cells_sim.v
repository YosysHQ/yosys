/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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

module VDD(output P);
  assign P = 1;
endmodule

module GND(output G);
  assign G = 0;
endmodule

module INBUF(
    output O,
    (* iopad_external_pin *)
    input I);
  parameter CCIO_EN = "TRUE";
  parameter CAPACITANCE = "DONT_CARE";
  parameter IBUF_DELAY_VALUE = "0";
  parameter IBUF_LOW_PWR = "TRUE";
  parameter IFD_DELAY_VALUE = "AUTO";
  parameter IOSTANDARD = "DEFAULT";
  assign O = I;
  specify
    (I => O) = 22;
  endspecify
endmodule

module IBUFG(
    output O,
    (* iopad_external_pin *)
    input I);
  parameter CAPACITANCE = "DONT_CARE";
  parameter IBUF_DELAY_VALUE = "0";
  parameter IBUF_LOW_PWR = "TRUE";
  parameter IOSTANDARD = "DEFAULT";
  assign O = I;
endmodule

module OUTBUF(
    (* iopad_external_pin *)
    output O,
    input I);
  parameter CAPACITANCE = "DONT_CARE";
  parameter IOSTANDARD = "DEFAULT";
  parameter DRIVE = 12;
  parameter SLEW = "SLOW";
  assign O = I;
  specify
    (I => O) = 22;
  endspecify
endmodule

module BUFG(
    (* clkbuf_driver *)
    output O,
    input I);
  assign O = I;
  specify
    // https://github.com/SymbiFlow/prjxray-db/blob/4bc6385ab300b1819848371f508185f57b649a0e/artix7/timings/CLK_BUFG_TOP_R.sdf#L11
    (I => O) = 96;
  endspecify
endmodule

module BUFGCTRL(
    (* clkbuf_driver *)
    output O,
    input I0, input I1,
    (* invertible_pin = "IS_S0_INVERTED" *)
    input S0,
    (* invertible_pin = "IS_S1_INVERTED" *)
    input S1,
    (* invertible_pin = "IS_CE0_INVERTED" *)
    input CE0,
    (* invertible_pin = "IS_CE1_INVERTED" *)
    input CE1,
    (* invertible_pin = "IS_IGNORE0_INVERTED" *)
    input IGNORE0,
    (* invertible_pin = "IS_IGNORE1_INVERTED" *)
    input IGNORE1);

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

module BUFHCE(
    (* clkbuf_driver *)
    output O,
    input I,
    (* invertible_pin = "IS_CE_INVERTED" *)
    input CE);

parameter [0:0] INIT_OUT = 1'b0;
parameter CE_TYPE = "SYNC";
parameter [0:0] IS_CE_INVERTED = 1'b0;

assign O = ((CE ^ IS_CE_INVERTED) ? I : INIT_OUT);

endmodule

module INV(
    (* clkbuf_inv = "I" *)
    output O,
    input I
);
  assign O = !I;
  specify
    (I => O) = 22;
  endspecify
endmodule

(* abc9_lut=1 *)
module LUT1(output O, input I0);
  parameter [1:0] INIT = 0;
  assign O = I0 ? INIT[1] : INIT[0];
  specify
    (I0 => O) = 22;
  endspecify
endmodule

(* abc9_lut=2 *)
module LUT2(output O, input I0, I1);
  parameter [3:0] INIT = 0;
  wire [ 1: 0] s1 = I1 ? INIT[ 3: 2] : INIT[ 1: 0];
  assign O = I0 ? s1[1] : s1[0];
  specify
    (I0 => O) = 22;
    (I1 => O) = 22;
  endspecify
endmodule

(* abc9_lut=3 *)
module LUT3(output O, input I0, I1, I2);
  parameter [7:0] INIT = 0;
  wire [ 3: 0] s2 = I2 ? INIT[ 7: 4] : INIT[ 3: 0];
  wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
  assign O = I0 ? s1[1] : s1[0];
  specify
    (I0 => O) = 22;
    (I1 => O) = 22;
    (I2 => O) = 22;
  endspecify
endmodule

(* abc9_lut=4 *)
module LUT4(output O, input I0, I1, I2, I3);
  parameter [15:0] INIT = 0;
  wire [ 7: 0] s3 = I3 ? INIT[15: 8] : INIT[ 7: 0];
  wire [ 3: 0] s2 = I2 ?   s3[ 7: 4] :   s3[ 3: 0];
  wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
  assign O = I0 ? s1[1] : s1[0];
  specify
    (I0 => O) = 22;
    (I1 => O) = 22;
    (I2 => O) = 22;
    (I3 => O) = 22;
  endspecify
endmodule

(* abc9_lut=5 *)
module LUT5(output O, input I0, I1, I2, I3, I4);
  parameter [31:0] INIT = 0;
  wire [15: 0] s4 = I4 ? INIT[31:16] : INIT[15: 0];
  wire [ 7: 0] s3 = I3 ?   s4[15: 8] :   s4[ 7: 0];
  wire [ 3: 0] s2 = I2 ?   s3[ 7: 4] :   s3[ 3: 0];
  wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
  assign O = I0 ? s1[1] : s1[0];
  specify
    (I0 => O) = 22;
    (I1 => O) = 22;
    (I2 => O) = 22;
    (I3 => O) = 22;
    (I4 => O) = 22;
  endspecify
endmodule

(* abc9_lut=6 *)
module LUT6(output O, input I0, I1, I2, I3, I4, I5);
  parameter [63:0] INIT = 0;
  wire [31: 0] s5 = I5 ? INIT[63:32] : INIT[31: 0];
  wire [15: 0] s4 = I4 ?   s5[31:16] :   s5[15: 0];
  wire [ 7: 0] s3 = I3 ?   s4[15: 8] :   s4[ 7: 0];
  wire [ 3: 0] s2 = I2 ?   s3[ 7: 4] :   s3[ 3: 0];
  wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
  assign O = I0 ? s1[1] : s1[0];
  specify
    (I0 => O) = 22;
    (I1 => O) = 22;
    (I2 => O) = 22;
    (I3 => O) = 22;
    (I4 => O) = 22;
    (I5 => O) = 22;
  endspecify
endmodule

module LUT6_D(output O6, output O5, input I0, I1, I2, I3, I4, I5);
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

// This is a placeholder for ABC9 to extract the area/delay
//   cost of 3-input LUTs and is not intended to be instantiated
(* abc9_lut=12 *)
module \$__ABC9_LUT7 (output O, input I0, I1, I2, I3, I4, I5, I6);
`ifndef __ICARUS__
  specify
    (I0 => O) = 22 + 63 /* LUTMUX7.I1 */;
    (I1 => O) = 22 + 63 /* LUTMUX7.I1 */;
    (I2 => O) = 22 + 63 /* LUTMUX7.I1 */;
    (I3 => O) = 22 + 63 /* LUTMUX7.I1 */;
    (I4 => O) = 22 + 63 /* LUTMUX7.I1 */;
    (I5 => O) = 22 + 63 /* LUTMUX7.I1 */;
    (I6 => O) = 0  + 51 /* LUTMUX7.S */;
  endspecify
`endif
endmodule

// This is a placeholder for ABC9 to extract the area/delay
//   cost of 3-input LUTs and is not intended to be instantiated
(* abc9_lut=24 *)
module \$__ABC9_LUT8 (output O, input I0, I1, I2, I3, I4, I5, I6, I7);
`ifndef __ICARUS__
  specify
    (I0 => O) = 22 + 63 /* LUTMUX7.I1 */ + 48 /* LUTMUX8.I0 */;
    (I1 => O) = 22 + 63 /* LUTMUX7.I1 */ + 48 /* LUTMUX8.I0 */;
    (I2 => O) = 22 + 63 /* LUTMUX7.I1 */ + 48 /* LUTMUX8.I0 */;
    (I3 => O) = 22 + 63 /* LUTMUX7.I1 */ + 48 /* LUTMUX8.I0 */;
    (I4 => O) = 22 + 63 /* LUTMUX7.I1 */ + 48 /* LUTMUX8.I0 */;
    (I5 => O) = 22 + 63 /* LUTMUX7.I1 */ + 48 /* LUTMUX8.I0 */;
    (I6 => O) = 0  + 51 /* LUTMUX7.S */  + 48 /* LUTMUX8.I0 */;
    (I7 => O) = 0  +  0                  + 58 /* LUTMUX8.S */;
  endspecify
`endif
endmodule

(* abc9_box, lib_whitebox *)
module LUTMUX7(output O, input I0, I1, S);
  assign O = S ? I1 : I0;
  specify
    (I0 => O) = 62;
    (I1 => O) = 63;
    (S => O) = 51;
  endspecify
endmodule

(* abc9_box, lib_whitebox *)
module LUTMUX8(output O, input I0, I1, S);
  assign O = S ? I1 : I0;
  specify
    (I0 => O) = 48;
    (I1 => O) = 46;
    (S => O) = 58;
  endspecify
endmodule

(* abc9_box, lib_whitebox *)
module CRY4(
  (* abc9_carry *)
  output [3:0] CO,
  output [3:0] O,
  (* abc9_carry *)
  input        CI,
  input        CYINIT,
  input  [3:0] DI, S
);
  assign O = S ^ {CO[2:0], CI | CYINIT};
  assign CO[0] = S[0] ? CI | CYINIT : DI[0];
  assign CO[1] = S[1] ? CO[0] : DI[1];
  assign CO[2] = S[2] ? CO[1] : DI[2];
  assign CO[3] = S[3] ? CO[2] : DI[3];
  specify
    // https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLL_L.sdf#L11-L46
    (S[0]   => O[0]) = 39;
    (CI     => O[0]) = 43;
    (DI[0]  => O[1]) = 81;
    (S[0]   => O[1]) = 61;
    (S[1]   => O[1]) = 42;
    (CI     => O[1]) = 50;
    (DI[0]  => O[2]) = 98;
    (DI[1]  => O[2]) = 95;
    (S[0]   => O[2]) = 70;
    (S[1]   => O[2]) = 75;
    (S[2]   => O[2]) = 48;
    (CI     => O[2]) = 64;
    (DI[0]  => O[3]) = 101;
    (DI[1]  => O[3]) = 120;
    (DI[2]  => O[3]) = 65;
    (S[0]   => O[3]) = 69;
    (S[1]   => O[3]) = 91;
    (S[2]   => O[3]) = 42;
    (S[3]   => O[3]) = 39;
    (CI     => O[3]) = 84;
    (DI[0]  => CO[0]) = 59;
    (S[0]   => CO[0]) = 43;
    (CI     => CO[0]) = 50;
    (DI[0]  => CO[1]) = 87;
    (DI[1]  => CO[1]) = 64;
    (S[0]   => CO[1]) = 63;
    (S[1]   => CO[1]) = 51;
    (CI     => CO[1]) = 55;
    (DI[0]  => CO[2]) = 103;
    (DI[1]  => CO[2]) = 113;
    (DI[2]  => CO[2]) = 58;
    (S[0]   => CO[2]) = 68;
    (S[1]   => CO[2]) = 79;
    (S[2]   => CO[2]) = 37;
    (CI     => CO[2]) = 77;
    (DI[0]  => CO[3]) = 93;
    (DI[1]  => CO[3]) = 95;
    (DI[2]  => CO[3]) = 84;
    (DI[3]  => CO[3]) = 72;
    (S[0]   => CO[3]) = 91;
    (S[1]   => CO[3]) = 97;
    (S[2]   => CO[3]) = 82;
    (S[3]   => CO[3]) = 81;
    (CI     => CO[3]) = 20;
  endspecify
endmodule

(* abc9_box, lib_whitebox *)
module CRY4INIT(
  (* abc9_carry *)
  output       CO,
  (* abc9_carry *)
  input        CYINIT
);
  specify
    (CYINIT => CO) = 72;
  endspecify

  assign CO = CYINIT;
endmodule

module ORCY (output O, input CI, I);
  assign O = CI | I;
endmodule

module MULT_AND (output LO, input I0, I1);
  assign LO = I0 & I1;
endmodule

// Flip-flops.

(* abc9_flop, lib_whitebox *)
module FFRE (
  output reg Q,
  (* clkbuf_sink *)
  input C,
  input CE,
  input D,
  input R
);
  parameter [0:0] INIT = 1'b0;
  initial Q <= INIT;
  always @(posedge C) if (R) Q <= 1'b0; else if (CE) Q <= D;
  specify
    $setup(D , posedge C, 31);
    $setup(CE, posedge C, 122);
    $setup(R , posedge C, 128);
    if (R)        (posedge C => (Q : 1'b0)) = 280;
    if (!R && CE) (posedge C => (Q : D)) = 280;
  endspecify
endmodule

(* abc9_flop, lib_whitebox *)
module FFRE_N (
  output reg Q,
  (* clkbuf_sink *)
  input C,
  input CE,
  input D,
  input R
);
  parameter [0:0] INIT = 1'b0;
  initial Q <= INIT;
  always @(negedge C) if (R) Q <= 1'b0; else if (CE) Q <= D;
  specify
    $setup(D , negedge C, 31);
    $setup(CE, negedge C, 122);
    $setup(R , negedge C, 128);
    if (R)        (negedge C => (Q : 1'b0)) = 280;
    if (!R && CE) (negedge C => (Q : D)) = 280;
  endspecify
endmodule

module FFSE (
  output reg Q,
  (* clkbuf_sink *)
  input C,
  input CE,
  input D,
  input S
);
  parameter [0:0] INIT = 1'b1;
  initial Q <= INIT;
  always @(posedge C) if (S) Q <= 1'b1; else if (CE) Q <= D;
  specify
    $setup(D , posedge C, 31);
    $setup(CE, posedge C, 122);
    $setup(S , posedge C, 128);
    if (S)        (negedge C => (Q : 1'b1)) = 280;
    if (!S && CE) (posedge C => (Q : D)) = 280;
  endspecify
endmodule

module FFSE_N (
  output reg Q,
  (* clkbuf_sink *)
  input C,
  input CE,
  input D,
  input S
);
  parameter [0:0] INIT = 1'b1;
  initial Q <= INIT;
  always @(negedge C) if (S) Q <= 1'b1; else if (CE) Q <= D;
  specify
    $setup(D , negedge C, 31);
    $setup(CE, negedge C, 122);
    $setup(S , negedge C, 128);
    if (S)        (negedge C => (Q : 1'b1)) = 280;
    if (!S && CE) (negedge C => (Q : D)) = 280;
  endspecify
endmodule

module FFCE (
  output reg Q,
  (* clkbuf_sink *)
  input C,
  input CE,
  input CLR,
  input D
);
  parameter [0:0] INIT = 1'b0;
  initial Q <= INIT;
  always @(posedge C, posedge CLR) if ( CLR) Q <= 1'b0; else if (CE) Q <= D;
  specify
    $setup(D , posedge C, 31);
    $setup(CE , posedge C, 122);
    if (!CLR && CE) (posedge C => (Q : D)) = 280;
  endspecify
endmodule

module FFCE_N (
  output reg Q,
  (* clkbuf_sink *)
  input C,
  input CE,
  input CLR,
  input D
);
  parameter [0:0] INIT = 1'b0;
  initial Q <= INIT;
  always @(negedge C, posedge CLR) if (CLR) Q <= 1'b0; else if (CE) Q <= D;
  specify
    $setup(D , negedge C, 31);
    $setup(CE , negedge C, 122);
    if (!CLR && CE) (negedge C => (Q : D)) = 280;
  endspecify
endmodule

module FFPE (
  output reg Q,
  (* clkbuf_sink *)
  input C,
  input CE,
  input PRE,
  input D
);
  parameter [0:0] INIT = 1'b1;
  initial Q <= INIT;
  always @(posedge C, posedge PRE) if ( PRE) Q <= 1'b1; else if (CE) Q <= D;
  specify
    $setup(D , posedge C, 31);
    $setup(CE , posedge C, 122);
    if (!PRE && CE) (posedge C => (Q : D)) = 291;
  endspecify
endmodule

module FFPE_N (
  output reg Q,
  (* clkbuf_sink *)
  input C,
  input CE,
  input PRE,
  input D
);
  parameter [0:0] INIT = 1'b1;
  initial Q <= INIT;
  always @(negedge C, posedge PRE) if (PRE) Q <= 1'b1; else if (CE) Q <= D;
  specify
    $setup(D , negedge C, 31);
    $setup(CE , negedge C, 122);
    if (!PRE && CE) (negedge C => (Q : D)) = 291;
  endspecify
endmodule

// LUTRAM.

// Single port.

(* abc9_box, lib_whitebox *)
module RAMS32X1 (
  output O,
  input A0, A1, A2, A3, A4,
  input D,
  (* clkbuf_sink *)
  input WCLK,
  input WE
);
  parameter [31:0] INIT = 32'h00000000;
  wire [4:0] a = {A4, A3, A2, A1, A0};
  reg [31:0] mem = INIT;
  assign O = mem[a];
  always @(posedge WCLK) if (WE) mem[a] <= D;
  specify
    $setup(A0, posedge WCLK, 0);
    $setup(A1, posedge WCLK, 0);
    $setup(A2, posedge WCLK, 0);
    $setup(A3, posedge WCLK, 0);
    $setup(A4, posedge WCLK, 0);
    $setup(D,  posedge WCLK, 0);
    $setup(WE, posedge WCLK, 0);
    (A0 => O) = 63;
    (A1 => O) = 63;
    (A2 => O) = 63;
    (A3 => O) = 63;
    (A4 => O) = 63;
    (posedge WCLK => (O : D)) = 813;
  endspecify
endmodule

(* abc9_box, lib_whitebox *)
module RAMS64X1 (
  output O,
  input A0, A1, A2, A3, A4, A5,
  input D,
  (* clkbuf_sink *)
  input WCLK,
  input WE
);
  parameter [63:0] INIT = 64'h0000000000000000;
  wire [5:0] a = {A5, A4, A3, A2, A1, A0};
  reg [63:0] mem = INIT;
  assign O = mem[a];
  always @(posedge WCLK) if (WE) mem[a] <= D;
  specify
    $setup(A0, posedge WCLK, 0);
    $setup(A1, posedge WCLK, 0);
    $setup(A2, posedge WCLK, 0);
    $setup(A3, posedge WCLK, 0);
    $setup(A4, posedge WCLK, 0);
    $setup(A5, posedge WCLK, 0);
    $setup(D,  posedge WCLK, 0);
    $setup(WE, posedge WCLK, 0);
    (A0 => O) = 161;
    (A1 => O) = 161;
    (A2 => O) = 161;
    (A3 => O) = 161;
    (A4 => O) = 161;
    (A5 => O) = 64;
    (posedge WCLK => (O : D)) = 762;
  endspecify
endmodule

(* abc9_box, lib_whitebox *)
module RAMD32X1 (
  output DPO, SPO,
  input  D,
  (* clkbuf_sink *)
  input  WCLK,
  input  WE,
  input  A0, A1, A2, A3, A4,
  input  DPRA0, DPRA1, DPRA2, DPRA3, DPRA4
);
  parameter INIT = 32'h0;
  wire [4:0] a = {A4, A3, A2, A1, A0};
  wire [4:0] dpra = {DPRA5, DPRA4, DPRA3, DPRA2, DPRA1, DPRA0};
  reg [31:0] mem = INIT;
  assign SPO = mem[a];
  assign DPO = mem[dpra];
  always @(posedge WCLK) if (WE) mem[a] <= D;
  specify
    $setup(A0, posedge WCLK, 0);
    $setup(A1, posedge WCLK, 0);
    $setup(A2, posedge WCLK, 0);
    $setup(A3, posedge WCLK, 0);
    $setup(A4, posedge WCLK, 0);
    // HACK: No timing arcs for DPRAn; using ones for An
    $setup(DPRA0, posedge WCLK, 0);
    $setup(DPRA1, posedge WCLK, 0);
    $setup(DPRA2, posedge WCLK, 0);
    $setup(DPRA3, posedge WCLK, 0);
    $setup(DPRA4, posedge WCLK, 0);
    $setup(D,  posedge WCLK, 0);
    $setup(WE, posedge WCLK, 0);
    // HACK: No timing arcs for SPO; using ones for DPO
    (A0 => SPO) = 66;
    (A1 => SPO) = 66;
    (A2 => SPO) = 66;
    (A3 => SPO) = 66;
    (A4 => SPO) = 66;
    (DPRA0 => DPO) = 66;
    (DPRA1 => DPO) = 66;
    (DPRA2 => DPO) = 66;
    (DPRA3 => DPO) = 66;
    (DPRA4 => DPO) = 66;
    (posedge WCLK => (SPO : D)) = 813;
    (posedge WCLK => (DPO : D)) = 813;
  endspecify
endmodule

(* abc9_box, lib_whitebox *)
module RAMD64X1 (
  output DPO, SPO,
  input  D,
  (* clkbuf_sink *)
  input  WCLK,
  input  WE,
  input  A0, A1, A2, A3, A4, A5,
  input  DPRA0, DPRA1, DPRA2, DPRA3, DPRA4, DPRA5
);
  parameter INIT = 64'h0;
  wire [5:0] a = {A5, A4, A3, A2, A1, A0};
  wire [5:0] dpra = {DPRA5, DPRA4, DPRA3, DPRA2, DPRA1, DPRA0};
  reg [63:0] mem = INIT;
  assign SPO = mem[a];
  assign DPO = mem[dpra];
  always @(posedge WCLK) if (WE) mem[a] <= D;
  specify
    $setup(A0, posedge WCLK, 0);
    $setup(A1, posedge WCLK, 0);
    $setup(A2, posedge WCLK, 0);
    $setup(A3, posedge WCLK, 0);
    $setup(A4, posedge WCLK, 0);
    $setup(A5, posedge WCLK, 0);
    // HACK: No timing arcs for DPRAn; using ones for An
    $setup(DPRA0, posedge WCLK, 0);
    $setup(DPRA1, posedge WCLK, 0);
    $setup(DPRA2, posedge WCLK, 0);
    $setup(DPRA3, posedge WCLK, 0);
    $setup(DPRA4, posedge WCLK, 0);
    $setup(DPRA5, posedge WCLK, 0);
    $setup(D,  posedge WCLK, 0);
    $setup(WE, posedge WCLK, 0);
    (A0 => SPO) = 161;
    (A1 => SPO) = 161;
    (A2 => SPO) = 161;
    (A3 => SPO) = 161;
    (A4 => SPO) = 161;
    (A5 => SPO) = 64;
    (DPRA0 => DPO) = 118;
    (DPRA1 => DPO) = 118;
    (DPRA2 => DPO) = 118;
    (DPRA3 => DPO) = 118;
    (DPRA4 => DPO) = 118;
    (DPRA5 => DPO) = 63;    
    (posedge WCLK => (SPO : D)) = 762;
    (posedge WCLK => (DPO : D)) = 737;
  endspecify
endmodule

// Shift registers.

(* abc9_box, lib_whitebox *)
module SRG16E (
  output Q,
  input A0, A1, A2, A3, CE,
  (* clkbuf_sink *)
  input CLK,
  input D
);
  parameter [15:0] INIT = 16'h0000;

  reg [15:0] r = INIT;
  assign Q = r[{A3,A2,A1,A0}];
  always @(posedge CLK) if (CE) r <= { r[14:0], D };
  specify
    $setup(D , posedge CLK, 173);
    if (CE) (posedge CLK => (Q : D)) = 1472;
    if (CE) (posedge CLK => (Q : 1'bx)) = 1472;
    (A0 => Q) = 631;
    (A1 => Q) = 472;
    (A2 => Q) = 407;
    (A3 => Q) = 238;
  endspecify
endmodule

// DSP

// Virtex 6, Series 7.

`ifdef YOSYS
(* abc9_box=!(PREG || AREG || ADREG || BREG || CREG || DREG || MREG)
`ifdef ALLOW_WHITEBOX_DSP48E1
   // Do not make DSP48E1 a whitebox for ABC9 even if fully combinatorial, since it is a big complex block
   , lib_whitebox=!(PREG || AREG || ADREG || BREG || CREG || DREG || MREG || INMODEREG || OPMODEREG || ALUMODEREG || CARRYINREG || CARRYINSELREG)
`endif
*)
`endif
module DSP48E1 (
    output [29:0] ACOUT,
    output [17:0] BCOUT,
    output reg CARRYCASCOUT,
    output reg [3:0] CARRYOUT,
    output reg MULTSIGNOUT,
    output OVERFLOW,
    output reg signed [47:0] P,
    output reg PATTERNBDETECT,
    output reg PATTERNDETECT,
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
    (* clkbuf_sink *) input CLK,
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

`ifdef YOSYS
    function integer \A.required ;
    begin
        if (AREG != 0)           \A.required =  254;
        else if (USE_MULT == "MULTIPLY" && USE_DPORT == "FALSE") begin
            if (MREG != 0)       \A.required = 1416;
            else if (PREG != 0)  \A.required = (USE_PATTERN_DETECT != "NO_PATDET" ? 3030 : 2739) ;
        end
        else if (USE_MULT == "MULTIPLY" && USE_DPORT == "TRUE") begin
            // Worst-case from ADREG and MREG
            if (MREG != 0)       \A.required = 2400;
            else if (ADREG != 0) \A.required = 1283;
            else if (PREG != 0)  \A.required = 3723;
            else if (PREG != 0)  \A.required = (USE_PATTERN_DETECT != "NO_PATDET" ? 4014 : 3723) ;
        end
        else if (USE_MULT == "NONE" && USE_DPORT == "FALSE") begin
            if (PREG != 0)       \A.required = (USE_PATTERN_DETECT != "NO_PATDET" ? 1730 : 1441) ;
        end
    end
    endfunction
    function integer \B.required ;
    begin
        if (BREG != 0)      \B.required =  324;
        else if (MREG != 0) \B.required = 1285;
        else if (USE_MULT == "MULTIPLY" && USE_DPORT == "FALSE") begin
            if (PREG != 0)  \B.required = (USE_PATTERN_DETECT != "NO_PATDET" ? 2898 : 2608) ;
        end
        else if (USE_MULT == "MULTIPLY" && USE_DPORT == "TRUE") begin
            if (PREG != 0)  \B.required = (USE_PATTERN_DETECT != "NO_PATDET" ? 2898 : 2608) ;
        end
        else if (USE_MULT == "NONE" && USE_DPORT == "FALSE") begin
            if (PREG != 0)  \B.required = (USE_PATTERN_DETECT != "NO_PATDET" ? 1718 : 1428) ;
        end
    end
    endfunction
    function integer \C.required ;
    begin
        if (CREG != 0)      \C.required =  168;
        else if (PREG != 0) \C.required = (USE_PATTERN_DETECT != "NO_PATDET" ? 1534 : 1244) ;
    end
    endfunction
    function integer \D.required ;
    begin
        if (USE_MULT == "MULTIPLY" && USE_DPORT == "FALSE") begin
        end
        else if (USE_MULT == "MULTIPLY" && USE_DPORT == "TRUE") begin
            if (DREG != 0)       \D.required =  248;
            else if (ADREG != 0) \D.required = 1195;
            else if (MREG != 0)  \D.required = 2310;
            else if (PREG != 0)  \D.required = (USE_PATTERN_DETECT != "NO_PATDET" ? 3925 : 3635) ;
        end
        else if (USE_MULT == "NONE" && USE_DPORT == "FALSE") begin
        end
    end
    endfunction
    function integer \P.arrival ;
    begin
        if (USE_MULT == "MULTIPLY" && USE_DPORT == "FALSE") begin
            if (PREG != 0)       \P.arrival =  329;
            // Worst-case from CREG and MREG
            else if (CREG != 0)  \P.arrival = 1687;
            else if (MREG != 0)  \P.arrival = 1671;
            // Worst-case from AREG and BREG
            else if (AREG != 0)  \P.arrival = 2952;
            else if (BREG != 0)  \P.arrival = 2813;
        end
        else if (USE_MULT == "MULTIPLY" && USE_DPORT == "TRUE") begin
            if (PREG != 0)       \P.arrival =  329;
            // Worst-case from CREG and MREG
            else if (CREG != 0)  \P.arrival = 1687;
            else if (MREG != 0)  \P.arrival = 1671;
            // Worst-case from AREG, ADREG, BREG, DREG
            else if (AREG != 0)  \P.arrival = 3935;
            else if (DREG != 0)  \P.arrival = 3908;
            else if (ADREG != 0) \P.arrival = 2958;
            else if (BREG != 0)  \P.arrival = 2813;
        end
        else if (USE_MULT == "NONE" && USE_DPORT == "FALSE") begin
            if (PREG != 0)       \P.arrival =  329;
            // Worst-case from AREG, BREG, CREG
            else if (CREG != 0)  \P.arrival = 1687;
            else if (AREG != 0)  \P.arrival = 1632;
            else if (BREG != 0)  \P.arrival = 1616;
        end
    end
    endfunction
    function integer \PCOUT.arrival ;
    begin
        if (USE_MULT == "MULTIPLY" && USE_DPORT == "FALSE") begin
            if (PREG != 0)       \PCOUT.arrival =  435;
            // Worst-case from CREG and MREG
            else if (CREG != 0)  \PCOUT.arrival = 1835;
            else if (MREG != 0)  \PCOUT.arrival = 1819;
            // Worst-case from AREG and BREG
            else if (AREG != 0)  \PCOUT.arrival = 3098;
            else if (BREG != 0)  \PCOUT.arrival = 2960;
        end
        else if (USE_MULT == "MULTIPLY" && USE_DPORT == "TRUE") begin
            if (PREG != 0)       \PCOUT.arrival =  435;
            // Worst-case from CREG and MREG
            else if (CREG != 0)  \PCOUT.arrival = 1835;
            else if (MREG != 0)  \PCOUT.arrival = 1819;
            // Worst-case from AREG, ADREG, BREG, DREG
            else if (AREG != 0)  \PCOUT.arrival = 4083;
            else if (DREG != 0)  \PCOUT.arrival = 4056;
            else if (BREG != 0)  \PCOUT.arrival = 2960;
            else if (ADREG != 0) \PCOUT.arrival = 2859;
        end
        else if (USE_MULT == "NONE" && USE_DPORT == "FALSE") begin
            if (PREG != 0)       \PCOUT.arrival =  435;
            // Worst-case from AREG, BREG, CREG
            else if (CREG != 0)  \PCOUT.arrival = 1835;
            else if (AREG != 0)  \PCOUT.arrival = 1780;
            else if (BREG != 0)  \PCOUT.arrival = 1765;
        end
    end
    endfunction
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

    generate
        if (PREG == 0 && MREG == 0 && AREG == 0 && ADREG == 0)
            specify
                (A *> P) =      \A.P.comb ();
                (A *> PCOUT) =  \A.PCOUT.comb ();
            endspecify
        else
            specify
                $setup(A, posedge CLK &&& !IS_CLK_INVERTED, \A.required () );
                $setup(A, negedge CLK &&&  IS_CLK_INVERTED, \A.required () );
            endspecify

        if (PREG == 0 && MREG == 0 && BREG == 0)
            specify
                (B *> P) =      \B.P.comb ();
                (B *> PCOUT) =  \B.PCOUT.comb ();
            endspecify
        else
            specify
                $setup(B, posedge CLK &&& !IS_CLK_INVERTED, \B.required () );
                $setup(B, negedge CLK &&&  IS_CLK_INVERTED, \B.required () );
            endspecify

        if (PREG == 0 && CREG == 0)
            specify
                (C *> P) =      \C.P.comb ();
                (C *> PCOUT) =  \C.PCOUT.comb ();
            endspecify
        else
            specify
                $setup(C, posedge CLK &&& !IS_CLK_INVERTED, \C.required () );
                $setup(C, negedge CLK &&&  IS_CLK_INVERTED, \C.required () );
            endspecify

        if (PREG == 0 && MREG == 0 && ADREG == 0 && DREG == 0)
            specify
                (D *> P) =      \D.P.comb ();
                (D *> PCOUT) =  \D.PCOUT.comb ();
            endspecify
        else
            specify
                $setup(D, posedge CLK &&& !IS_CLK_INVERTED, \D.required () );
                $setup(D, negedge CLK &&&  IS_CLK_INVERTED, \D.required () );
            endspecify

        if (PREG == 0)
            specify
                (PCIN *> P) =       1107;
                (PCIN *> PCOUT) =   1255;
            endspecify
        else
            specify
                $setup(PCIN, posedge CLK &&& !IS_CLK_INVERTED, USE_PATTERN_DETECT != "NO_PATDET" ? 1315 : 1025);
                $setup(PCIN, negedge CLK &&&  IS_CLK_INVERTED, USE_PATTERN_DETECT != "NO_PATDET" ? 1315 : 1025);
            endspecify

        if (PREG || AREG || ADREG || BREG || CREG || DREG || MREG)
            specify
                if (!IS_CLK_INVERTED && CEP) (posedge CLK => (P : 48'bx)) = \P.arrival () ;
                if ( IS_CLK_INVERTED && CEP) (negedge CLK => (P : 48'bx)) = \P.arrival () ;
                if (!IS_CLK_INVERTED && CEP) (posedge CLK => (PCOUT : 48'bx)) = \PCOUT.arrival () ;
                if ( IS_CLK_INVERTED && CEP) (negedge CLK => (PCOUT : 48'bx)) = \PCOUT.arrival () ;
            endspecify
    endgenerate
`endif

    initial begin
`ifndef YOSYS
        if (AUTORESET_PATDET != "NO_RESET") $fatal(1, "Unsupported AUTORESET_PATDET value");
        if (SEL_MASK != "MASK")     $fatal(1, "Unsupported SEL_MASK value");
        if (SEL_PATTERN != "PATTERN") $fatal(1, "Unsupported SEL_PATTERN value");
        if (USE_SIMD != "ONE48" && USE_SIMD != "TWO24" && USE_SIMD != "FOUR12")    $fatal(1, "Unsupported USE_SIMD value");
        if (IS_ALUMODE_INVERTED != 4'b0) $fatal(1, "Unsupported IS_ALUMODE_INVERTED value");
        if (IS_CARRYIN_INVERTED != 1'b0) $fatal(1, "Unsupported IS_CARRYIN_INVERTED value");
        if (IS_CLK_INVERTED != 1'b0) $fatal(1, "Unsupported IS_CLK_INVERTED value");
        if (IS_INMODE_INVERTED != 5'b0) $fatal(1, "Unsupported IS_INMODE_INVERTED value");
        if (IS_OPMODE_INVERTED != 7'b0) $fatal(1, "Unsupported IS_OPMODE_INVERTED value");
`endif
    end

    wire signed [29:0] A_muxed;
    wire signed [17:0] B_muxed;

    generate
        if (A_INPUT == "CASCADE") assign A_muxed = ACIN;
        else assign A_muxed = A;

        if (B_INPUT == "CASCADE") assign B_muxed = BCIN;
        else assign B_muxed = B;
    endgenerate

    reg signed [29:0] Ar1, Ar2;
    reg signed [24:0] Dr;
    reg signed [17:0] Br1, Br2;
    reg signed [47:0] Cr;
    reg        [4:0]  INMODEr;
    reg        [6:0]  OPMODEr;
    reg        [3:0]  ALUMODEr;
    reg        [2:0]  CARRYINSELr;

    generate
        // Configurable A register
        if (AREG == 2) begin
            initial Ar1 = 30'b0;
            initial Ar2 = 30'b0;
            always @(posedge CLK)
                if (RSTA) begin
                    Ar1 <= 30'b0;
                    Ar2 <= 30'b0;
                end else begin
                    if (CEA1) Ar1 <= A_muxed;
                    if (CEA2) Ar2 <= Ar1;
                end
        end else if (AREG == 1) begin
            //initial Ar1 = 30'b0;
            initial Ar2 = 30'b0;
            always @(posedge CLK)
                if (RSTA) begin
                    Ar1 <= 30'b0;
                    Ar2 <= 30'b0;
                end else begin
                    if (CEA1) Ar1 <= A_muxed;
                    if (CEA2) Ar2 <= A_muxed;
                end
        end else begin
            always @* Ar1 <= A_muxed;
            always @* Ar2 <= A_muxed;
        end

        // Configurable B register
        if (BREG == 2) begin
            initial Br1 = 25'b0;
            initial Br2 = 25'b0;
            always @(posedge CLK)
                if (RSTB) begin
                    Br1 <= 18'b0;
                    Br2 <= 18'b0;
                end else begin
                    if (CEB1) Br1 <= B_muxed;
                    if (CEB2) Br2 <= Br1;
                end
        end else if (BREG == 1) begin
            //initial Br1 = 18'b0;
            initial Br2 = 18'b0;
            always @(posedge CLK)
                if (RSTB) begin
                    Br1 <= 18'b0;
                    Br2 <= 18'b0;
                end else begin
                    if (CEB1) Br1 <= B_muxed;
                    if (CEB2) Br2 <= B_muxed;
                end
        end else begin
            always @* Br1 <= B_muxed;
            always @* Br2 <= B_muxed;
        end

        // C and D registers
        if (CREG == 1) initial Cr = 48'b0;
        if (CREG == 1) begin always @(posedge CLK) if (RSTC) Cr <= 48'b0; else if (CEC) Cr <= C; end
        else           always @* Cr <= C;

	if (DREG == 1) initial Dr = 25'b0;
        if (DREG == 1) begin always @(posedge CLK) if (RSTD) Dr <= 25'b0; else if (CED) Dr <= D; end
        else           always @* Dr <= D;

        // Control registers
        if (INMODEREG == 1) initial INMODEr = 5'b0;
        if (INMODEREG == 1) begin always @(posedge CLK) if (RSTINMODE) INMODEr <= 5'b0; else if (CEINMODE) INMODEr <= INMODE; end
        else           always @* INMODEr <= INMODE;
        if (OPMODEREG == 1) initial OPMODEr = 7'b0;
        if (OPMODEREG == 1) begin always @(posedge CLK) if (RSTCTRL) OPMODEr <= 7'b0; else if (CECTRL) OPMODEr <= OPMODE; end
        else           always @* OPMODEr <= OPMODE;
        if (ALUMODEREG == 1) initial ALUMODEr = 4'b0;
        if (ALUMODEREG == 1) begin always @(posedge CLK) if (RSTALUMODE) ALUMODEr <= 4'b0; else if (CEALUMODE) ALUMODEr <= ALUMODE; end
        else           always @* ALUMODEr <= ALUMODE;
        if (CARRYINSELREG == 1) initial CARRYINSELr = 3'b0;
        if (CARRYINSELREG == 1) begin always @(posedge CLK) if (RSTCTRL) CARRYINSELr <= 3'b0; else if (CECTRL) CARRYINSELr <= CARRYINSEL; end
        else           always @* CARRYINSELr <= CARRYINSEL;
    endgenerate

    // A and B cascade
    generate
        if (ACASCREG == 1 && AREG == 2) assign ACOUT = Ar1;
        else assign ACOUT = Ar2;
        if (BCASCREG == 1 && BREG == 2) assign BCOUT = Br1;
        else assign BCOUT = Br2;
    endgenerate

    // A/D input selection and pre-adder
    wire signed [24:0] Ar12_muxed = INMODEr[0] ? Ar1 : Ar2;
    wire signed [24:0] Ar12_gated = INMODEr[1] ? 25'b0 : Ar12_muxed;
    wire signed [24:0] Dr_gated   = INMODEr[2] ? Dr : 25'b0;
    wire signed [24:0] AD_result  = INMODEr[3] ? (Dr_gated - Ar12_gated) : (Dr_gated + Ar12_gated);
    reg  signed [24:0] ADr;

    generate
        if (ADREG == 1) initial ADr = 25'b0;
        if (ADREG == 1) begin always @(posedge CLK) if (RSTD) ADr <= 25'b0; else if (CEAD) ADr <= AD_result; end
        else            always @* ADr <= AD_result;
    endgenerate

    // 25x18 multiplier
    wire signed [24:0] A_MULT;
    wire signed [17:0] B_MULT = INMODEr[4] ? Br1 : Br2;
    generate
        if (USE_DPORT == "TRUE") assign A_MULT = ADr;
        else assign A_MULT = Ar12_gated;
    endgenerate

    wire signed [42:0] M = A_MULT * B_MULT;
    wire signed [42:0] Mx = (CARRYINSEL == 3'b010) ? 43'bx : M;
    reg  signed [42:0] Mr = 43'b0;

    // Multiplier result register
    generate
        if (MREG == 1) begin always @(posedge CLK) if (RSTM) Mr <= 43'b0; else if (CEM) Mr <= Mx; end
        else           always @* Mr <= Mx;
    endgenerate

    wire signed [42:0] Mrx = (CARRYINSELr == 3'b010) ? 43'bx : Mr;

    // X, Y and Z ALU inputs
    reg signed [47:0] X, Y, Z;

    always @* begin
        // X multiplexer
        case (OPMODEr[1:0])
            2'b00: X = 48'b0;
            2'b01: begin X = $signed(Mrx);
`ifndef YOSYS
                if (OPMODEr[3:2] != 2'b01) $fatal(1, "OPMODEr[3:2] must be 2'b01 when OPMODEr[1:0] is 2'b01");
`endif
            end
            2'b10:
                if (PREG == 1)
                    X = P;
                else begin
                    X = 48'bx;
`ifndef YOSYS
                    $fatal(1, "PREG must be 1 when OPMODEr[1:0] is 2'b10");
`endif
                end
            2'b11: X = $signed({Ar2, Br2});
            default: X = 48'bx;
        endcase

        // Y multiplexer
        case (OPMODEr[3:2])
            2'b00: Y = 48'b0;
            2'b01: begin Y = 48'b0; // FIXME: more accurate partial product modelling?
`ifndef YOSYS
                if (OPMODEr[1:0] != 2'b01) $fatal(1, "OPMODEr[1:0] must be 2'b01 when OPMODEr[3:2] is 2'b01");
`endif
            end
            2'b10: Y = {48{1'b1}};
            2'b11: Y = Cr;
            default: Y = 48'bx;
        endcase

        // Z multiplexer
        case (OPMODEr[6:4])
            3'b000: Z = 48'b0;
            3'b001: Z = PCIN;
            3'b010:
                if (PREG == 1)
                    Z = P;
                else begin
                    Z = 48'bx;
`ifndef YOSYS
                    $fatal(1, "PREG must be 1 when OPMODEr[6:4] is 3'b010");
`endif
                end
            3'b011: Z = Cr;
            3'b100:
                if (PREG == 1 && OPMODEr[3:0] === 4'b1000)
                    Z = P;
                else begin
                    Z = 48'bx;
`ifndef YOSYS
                    if (PREG != 1) $fatal(1, "PREG must be 1 when OPMODEr[6:4] is 3'b100");
                    if (OPMODEr[3:0] != 4'b1000) $fatal(1, "OPMODEr[3:0] must be 4'b1000 when OPMODEr[6:4] i0s 3'b100");
`endif
                end
            3'b101: Z = $signed(PCIN[47:17]);
            3'b110:
                if (PREG == 1)
                    Z = $signed(P[47:17]);
                else begin
                    Z = 48'bx;
`ifndef YOSYS
                    $fatal(1, "PREG must be 1 when OPMODEr[6:4] is 3'b110");
`endif
                end
            default: Z = 48'bx;
        endcase
    end

    // Carry in
    wire A24_xnor_B17d = A_MULT[24] ~^ B_MULT[17];
    reg CARRYINr, A24_xnor_B17;
    generate
        if (CARRYINREG == 1) initial CARRYINr = 1'b0;
        if (CARRYINREG == 1) begin always @(posedge CLK) if (RSTALLCARRYIN) CARRYINr <= 1'b0; else if (CECARRYIN) CARRYINr <= CARRYIN; end
        else                 always @* CARRYINr = CARRYIN;

        if (MREG == 1) initial A24_xnor_B17 = 1'b0;
        if (MREG == 1) begin always @(posedge CLK) if (RSTALLCARRYIN) A24_xnor_B17 <= 1'b0; else if (CEM) A24_xnor_B17 <= A24_xnor_B17d; end
        else                 always @* A24_xnor_B17 = A24_xnor_B17d;
    endgenerate

    reg cin_muxed;

    always @(*) begin
        case (CARRYINSELr)
            3'b000: cin_muxed = CARRYINr;
            3'b001: cin_muxed = ~PCIN[47];
            3'b010: cin_muxed = CARRYCASCIN;
            3'b011: cin_muxed = PCIN[47];
            3'b100:
                if (PREG == 1)
                    cin_muxed = CARRYCASCOUT;
                else begin
                    cin_muxed = 1'bx;
`ifndef YOSYS
                    $fatal(1, "PREG must be 1 when CARRYINSEL is 3'b100");
`endif
                end
            3'b101:
                if (PREG == 1)
                    cin_muxed = ~P[47];
                else begin
                    cin_muxed = 1'bx;
`ifndef YOSYS
                    $fatal(1, "PREG must be 1 when CARRYINSEL is 3'b101");
`endif
                end
            3'b110: cin_muxed = A24_xnor_B17;
            3'b111:
                if (PREG == 1)
                    cin_muxed = P[47];
                else begin
                    cin_muxed = 1'bx;
`ifndef YOSYS
                    $fatal(1, "PREG must be 1 when CARRYINSEL is 3'b111");
`endif
                end
            default: cin_muxed = 1'bx;
        endcase
    end

    wire alu_cin = (ALUMODEr[3] || ALUMODEr[2]) ? 1'b0 : cin_muxed;

    // ALU core
    wire [47:0] Z_muxinv = ALUMODEr[0] ? ~Z : Z;
    wire [47:0] xor_xyz = X ^ Y ^ Z_muxinv;
    wire [47:0] maj_xyz = (X & Y) | (X & Z_muxinv) | (Y & Z_muxinv);

    wire [47:0] xor_xyz_muxed = ALUMODEr[3] ? maj_xyz : xor_xyz;
    wire [47:0] maj_xyz_gated = ALUMODEr[2] ? 48'b0 :  maj_xyz;

    wire [48:0] maj_xyz_simd_gated;
    wire [3:0] int_carry_in, int_carry_out, ext_carry_out;
    wire [47:0] alu_sum;
    assign int_carry_in[0] = 1'b0;
    wire [3:0] carryout_reset;

    generate
        if (USE_SIMD == "FOUR12") begin
            assign maj_xyz_simd_gated = {
                    maj_xyz_gated[47:36],
                    1'b0, maj_xyz_gated[34:24],
                    1'b0, maj_xyz_gated[22:12],
                    1'b0, maj_xyz_gated[10:0],
                    alu_cin
                };
            assign int_carry_in[3:1] = 3'b000;
            assign ext_carry_out = {
                    int_carry_out[3],
                    maj_xyz_gated[35] ^ int_carry_out[2],
                    maj_xyz_gated[23] ^ int_carry_out[1],
                    maj_xyz_gated[11] ^ int_carry_out[0]
                };
            assign carryout_reset = 4'b0000;
        end else if (USE_SIMD == "TWO24") begin
            assign maj_xyz_simd_gated = {
                    maj_xyz_gated[47:24],
                    1'b0, maj_xyz_gated[22:0],
                    alu_cin
                };
            assign int_carry_in[3:1] = {int_carry_out[2], 1'b0, int_carry_out[0]};
            assign ext_carry_out = {
                    int_carry_out[3],
                    1'bx,
                    maj_xyz_gated[23] ^ int_carry_out[1],
                    1'bx
                };
            assign carryout_reset = 4'b0x0x;
        end else begin
            assign maj_xyz_simd_gated = {maj_xyz_gated, alu_cin};
            assign int_carry_in[3:1] = int_carry_out[2:0];
            assign ext_carry_out = {
                    int_carry_out[3],
                    3'bxxx
                };
            assign carryout_reset = 4'b0xxx;
        end

        genvar i;
        for (i = 0; i < 4; i = i + 1)
            assign {int_carry_out[i], alu_sum[i*12 +: 12]} = {1'b0, maj_xyz_simd_gated[i*12 +: ((i == 3) ? 13 : 12)]}
                                                              + xor_xyz_muxed[i*12 +: 12] + int_carry_in[i];
    endgenerate

    wire signed [47:0] Pd = ALUMODEr[1] ? ~alu_sum : alu_sum;
    wire [3:0] CARRYOUTd = (OPMODEr[3:0] == 4'b0101 || ALUMODEr[3:2] != 2'b00) ? 4'bxxxx :
                           ((ALUMODEr[0] & ALUMODEr[1]) ? ~ext_carry_out : ext_carry_out);
    wire CARRYCASCOUTd = ext_carry_out[3];
    wire MULTSIGNOUTd = Mrx[42];

    generate
        if (PREG == 1) begin
            initial P = 48'b0;
            initial CARRYOUT = carryout_reset;
            initial CARRYCASCOUT = 1'b0;
            initial MULTSIGNOUT = 1'b0;
            always @(posedge CLK)
                if (RSTP) begin
                    P <= 48'b0;
                    CARRYOUT <= carryout_reset;
                    CARRYCASCOUT <= 1'b0;
                    MULTSIGNOUT <= 1'b0;
                end else if (CEP) begin
                    P <= Pd;
                    CARRYOUT <= CARRYOUTd;
                    CARRYCASCOUT <= CARRYCASCOUTd;
                    MULTSIGNOUT <= MULTSIGNOUTd;
                end
        end else begin
            always @* begin
                P = Pd;
                CARRYOUT = CARRYOUTd;
                CARRYCASCOUT = CARRYCASCOUTd;
                MULTSIGNOUT = MULTSIGNOUTd;
            end
        end
    endgenerate

    assign PCOUT = P;

    generate
        wire PATTERNDETECTd, PATTERNBDETECTd;

        if (USE_PATTERN_DETECT == "PATDET") begin
            // TODO: Support SEL_PATTERN != "PATTERN" and SEL_MASK != "MASK
            assign PATTERNDETECTd = &(~(Pd ^ PATTERN) | MASK);
            assign PATTERNBDETECTd = &((Pd ^ PATTERN) | MASK);
        end else begin
            assign PATTERNDETECTd = 1'b1;
            assign PATTERNBDETECTd = 1'b1;
        end

        if (PREG == 1) begin
            reg PATTERNDETECTPAST, PATTERNBDETECTPAST;
            initial PATTERNDETECT = 1'b0;
            initial PATTERNBDETECT = 1'b0;
            initial PATTERNDETECTPAST = 1'b0;
            initial PATTERNBDETECTPAST = 1'b0;
            always @(posedge CLK)
                if (RSTP) begin
                    PATTERNDETECT <= 1'b0;
                    PATTERNBDETECT <= 1'b0;
                    PATTERNDETECTPAST <= 1'b0;
                    PATTERNBDETECTPAST <= 1'b0;
                end else if (CEP) begin
                    PATTERNDETECT <= PATTERNDETECTd;
                    PATTERNBDETECT <= PATTERNBDETECTd;
                    PATTERNDETECTPAST <= PATTERNDETECT;
                    PATTERNBDETECTPAST <= PATTERNBDETECT;
                end
            assign OVERFLOW = &{PATTERNDETECTPAST, ~PATTERNBDETECT, ~PATTERNDETECT};
            assign UNDERFLOW = &{PATTERNBDETECTPAST, ~PATTERNBDETECT, ~PATTERNDETECT};
        end else begin
            always @* begin
                PATTERNDETECT = PATTERNDETECTd;
                PATTERNBDETECT = PATTERNBDETECTd;
            end
            assign OVERFLOW = 1'bx, UNDERFLOW = 1'bx;
        end
    endgenerate

endmodule

// Block RAM

module RAMB18E1 (
    (* clkbuf_sink *)
    (* invertible_pin = "IS_CLKARDCLK_INVERTED" *)
    input CLKARDCLK,
    (* clkbuf_sink *)
    (* invertible_pin = "IS_CLKBWRCLK_INVERTED" *)
    input CLKBWRCLK,
    (* invertible_pin = "IS_ENARDEN_INVERTED" *)
    input ENARDEN,
    (* invertible_pin = "IS_ENBWREN_INVERTED" *)
    input ENBWREN,
    input REGCEAREGCE,
    input REGCEB,
    (* invertible_pin = "IS_RSTRAMARSTRAM_INVERTED" *)
    input RSTRAMARSTRAM,
    (* invertible_pin = "IS_RSTRAMB_INVERTED" *)
    input RSTRAMB,
    (* invertible_pin = "IS_RSTREGARSTREG_INVERTED" *)
    input RSTREGARSTREG,
    (* invertible_pin = "IS_RSTREGB_INVERTED" *)
    input RSTREGB,
    input [13:0] ADDRARDADDR,
    input [13:0] ADDRBWRADDR,
    input [15:0] DIADI,
    input [15:0] DIBDI,
    input [1:0] DIPADIP,
    input [1:0] DIPBDIP,
    input [1:0] WEA,
    input [3:0] WEBWE,
    output [15:0] DOADO,
    output [15:0] DOBDO,
    output [1:0] DOPADOP,
    output [1:0] DOPBDOP
);
    parameter integer DOA_REG = 0;
    parameter integer DOB_REG = 0;
    parameter INITP_00 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INITP_01 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INITP_02 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INITP_03 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INITP_04 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INITP_05 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INITP_06 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INITP_07 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_00 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_01 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_02 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_03 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_04 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_05 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_06 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_07 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_08 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_09 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_0A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_0B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_0C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_0D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_0E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_0F = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_10 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_11 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_12 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_13 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_14 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_15 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_16 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_17 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_18 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_19 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_1A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_1B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_1C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_1D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_1E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_1F = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_20 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_21 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_22 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_23 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_24 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_25 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_26 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_27 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_28 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_29 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_2A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_2B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_2C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_2D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_2E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_2F = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_30 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_31 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_32 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_33 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_34 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_35 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_36 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_37 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_38 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_39 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_3A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_3B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_3C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_3D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_3E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_3F = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_A = 18'h0;
    parameter INIT_B = 18'h0;
    parameter INIT_FILE = "NONE";
    parameter RAM_MODE = "TDP";
    parameter RDADDR_COLLISION_HWCONFIG = "DELAYED_WRITE";
    parameter integer READ_WIDTH_A = 0;
    parameter integer READ_WIDTH_B = 0;
    parameter RSTREG_PRIORITY_A = "RSTREG";
    parameter RSTREG_PRIORITY_B = "RSTREG";
    parameter SIM_COLLISION_CHECK = "ALL";
    parameter SIM_DEVICE = "VIRTEX6";
    parameter SRVAL_A = 18'h0;
    parameter SRVAL_B = 18'h0;
    parameter WRITE_MODE_A = "WRITE_FIRST";
    parameter WRITE_MODE_B = "WRITE_FIRST";
    parameter integer WRITE_WIDTH_A = 0;
    parameter integer WRITE_WIDTH_B = 0;
    parameter IS_CLKARDCLK_INVERTED = 1'b0;
    parameter IS_CLKBWRCLK_INVERTED = 1'b0;
    parameter IS_ENARDEN_INVERTED = 1'b0;
    parameter IS_ENBWREN_INVERTED = 1'b0;
    parameter IS_RSTRAMARSTRAM_INVERTED = 1'b0;
    parameter IS_RSTRAMB_INVERTED = 1'b0;
    parameter IS_RSTREGARSTREG_INVERTED = 1'b0;
    parameter IS_RSTREGB_INVERTED = 1'b0;

    specify
        // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/BRAM_L.sdf#L13
        $setup(ADDRARDADDR, posedge CLKARDCLK, 566);
        // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/BRAM_L.sdf#L17
        $setup(ADDRBWRADDR, posedge CLKBWRCLK, 566);
        // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/BRAM_L.sdf#L19
        $setup(WEA, posedge CLKARDCLK, 532);
        // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/BRAM_L.sdf#L21
        $setup(WEBWE, posedge CLKBWRCLK, 532);
        // https://github.com/SymbiFlow/prjxray-db/blob/4bc6385ab300b1819848371f508185f57b649a0e/artix7/timings/BRAM_L.sdf#L29
        $setup(REGCEAREGCE, posedge CLKARDCLK, 360);
        // https://github.com/SymbiFlow/prjxray-db/blob/4bc6385ab300b1819848371f508185f57b649a0e/artix7/timings/BRAM_L.sdf#L31
        $setup(RSTREGARSTREG, posedge CLKARDCLK, 342);
        // https://github.com/SymbiFlow/prjxray-db/blob/4bc6385ab300b1819848371f508185f57b649a0e/artix7/timings/BRAM_L.sdf#L49
        $setup(REGCEB, posedge CLKBWRCLK, 360);
        // https://github.com/SymbiFlow/prjxray-db/blob/4bc6385ab300b1819848371f508185f57b649a0e/artix7/timings/BRAM_L.sdf#L59
        $setup(RSTREGB, posedge CLKBWRCLK, 342);
        // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/BRAM_L.sdf#L123
        $setup(DIADI, posedge CLKARDCLK, 737);
        // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/BRAM_L.sdf#L133
        $setup(DIBDI, posedge CLKBWRCLK, 737);
        // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/BRAM_L.sdf#L125
        $setup(DIPADIP, posedge CLKARDCLK, 737);
        // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/BRAM_L.sdf#L135
        $setup(DIPBDIP, posedge CLKBWRCLK, 737);
        // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/BRAM_L.sdf#L143
        if (&DOA_REG) (posedge CLKARDCLK => (DOADO : 16'bx)) = 2454;
        // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/BRAM_L.sdf#L144
        if (&DOA_REG) (posedge CLKARDCLK => (DOPADOP : 2'bx)) = 2454;
        // https://github.com/SymbiFlow/prjxray-db/blob/4bc6385ab300b1819848371f508185f57b649a0e/artix7/timings/BRAM_L.sdf#L153
        if (|DOA_REG) (posedge CLKARDCLK => (DOADO : 16'bx)) = 882;
        // https://github.com/SymbiFlow/prjxray-db/blob/4bc6385ab300b1819848371f508185f57b649a0e/artix7/timings/BRAM_L.sdf#L154
        if (|DOA_REG) (posedge CLKARDCLK => (DOPADOP : 2'bx)) = 882;
        // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/BRAM_L.sdf#L163
        if (&DOB_REG) (posedge CLKBWRCLK => (DOBDO : 16'bx)) = 2454;
        // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/BRAM_L.sdf#L164
        if (&DOB_REG) (posedge CLKBWRCLK => (DOPBDOP : 2'bx)) = 2454;
        // https://github.com/SymbiFlow/prjxray-db/blob/4bc6385ab300b1819848371f508185f57b649a0e/artix7/timings/BRAM_L.sdf#L173
        if (|DOB_REG) (posedge CLKBWRCLK => (DOBDO : 16'bx)) = 882;
        // https://github.com/SymbiFlow/prjxray-db/blob/4bc6385ab300b1819848371f508185f57b649a0e/artix7/timings/BRAM_L.sdf#L174
        if (|DOB_REG) (posedge CLKBWRCLK => (DOPBDOP : 2'bx)) = 882;
    endspecify
endmodule

module RAMB36E1 (
    output CASCADEOUTA,
    output CASCADEOUTB,
    output [31:0] DOADO,
    output [31:0] DOBDO,
    output [3:0] DOPADOP,
    output [3:0] DOPBDOP,
    output [7:0] ECCPARITY,
    output [8:0] RDADDRECC,
    output SBITERR,
    output DBITERR,
    (* invertible_pin = "IS_ENARDEN_INVERTED" *)
    input ENARDEN,
    (* clkbuf_sink *)
    (* invertible_pin = "IS_CLKARDCLK_INVERTED" *)
    input CLKARDCLK,
    (* invertible_pin = "IS_RSTRAMARSTRAM_INVERTED" *)
    input RSTRAMARSTRAM,
    (* invertible_pin = "IS_RSTREGARSTREG_INVERTED" *)
    input RSTREGARSTREG,
    input CASCADEINA,
    input REGCEAREGCE,
    (* invertible_pin = "IS_ENBWREN_INVERTED" *)
    input ENBWREN,
    (* clkbuf_sink *)
    (* invertible_pin = "IS_CLKBWRCLK_INVERTED" *)
    input CLKBWRCLK,
    (* invertible_pin = "IS_RSTRAMB_INVERTED" *)
    input RSTRAMB,
    (* invertible_pin = "IS_RSTREGB_INVERTED" *)
    input RSTREGB,
    input CASCADEINB,
    input REGCEB,
    input INJECTDBITERR,
    input INJECTSBITERR,
    input [15:0] ADDRARDADDR,
    input [15:0] ADDRBWRADDR,
    input [31:0] DIADI,
    input [31:0] DIBDI,
    input [3:0] DIPADIP,
    input [3:0] DIPBDIP,
    input [3:0] WEA,
    input [7:0] WEBWE
);
    parameter integer DOA_REG = 0;
    parameter integer DOB_REG = 0;
    parameter EN_ECC_READ = "FALSE";
    parameter EN_ECC_WRITE = "FALSE";
    parameter INITP_00 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INITP_01 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INITP_02 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INITP_03 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INITP_04 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INITP_05 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INITP_06 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INITP_07 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INITP_08 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INITP_09 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INITP_0A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INITP_0B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INITP_0C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INITP_0D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INITP_0E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INITP_0F = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_00 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_01 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_02 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_03 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_04 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_05 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_06 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_07 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_08 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_09 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_0A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_0B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_0C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_0D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_0E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_0F = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_10 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_11 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_12 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_13 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_14 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_15 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_16 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_17 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_18 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_19 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_1A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_1B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_1C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_1D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_1E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_1F = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_20 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_21 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_22 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_23 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_24 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_25 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_26 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_27 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_28 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_29 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_2A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_2B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_2C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_2D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_2E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_2F = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_30 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_31 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_32 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_33 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_34 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_35 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_36 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_37 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_38 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_39 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_3A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_3B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_3C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_3D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_3E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_3F = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_40 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_41 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_42 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_43 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_44 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_45 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_46 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_47 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_48 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_49 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_4A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_4B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_4C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_4D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_4E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_4F = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_50 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_51 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_52 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_53 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_54 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_55 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_56 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_57 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_58 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_59 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_5A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_5B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_5C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_5D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_5E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_5F = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_60 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_61 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_62 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_63 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_64 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_65 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_66 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_67 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_68 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_69 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_6A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_6B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_6C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_6D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_6E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_6F = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_70 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_71 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_72 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_73 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_74 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_75 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_76 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_77 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_78 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_79 = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_7A = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_7B = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_7C = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_7D = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_7E = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_7F = 256'h0000000000000000000000000000000000000000000000000000000000000000;
    parameter INIT_A = 36'h0;
    parameter INIT_B = 36'h0;
    parameter INIT_FILE = "NONE";
    parameter RAM_EXTENSION_A = "NONE";
    parameter RAM_EXTENSION_B = "NONE";
    parameter RAM_MODE = "TDP";
    parameter RDADDR_COLLISION_HWCONFIG = "DELAYED_WRITE";
    parameter integer READ_WIDTH_A = 0;
    parameter integer READ_WIDTH_B = 0;
    parameter RSTREG_PRIORITY_A = "RSTREG";
    parameter RSTREG_PRIORITY_B = "RSTREG";
    parameter SIM_COLLISION_CHECK = "ALL";
    parameter SIM_DEVICE = "VIRTEX6";
    parameter SRVAL_A = 36'h0;
    parameter SRVAL_B = 36'h0;
    parameter WRITE_MODE_A = "WRITE_FIRST";
    parameter WRITE_MODE_B = "WRITE_FIRST";
    parameter integer WRITE_WIDTH_A = 0;
    parameter integer WRITE_WIDTH_B = 0;
    parameter IS_CLKARDCLK_INVERTED = 1'b0;
    parameter IS_CLKBWRCLK_INVERTED = 1'b0;
    parameter IS_ENARDEN_INVERTED = 1'b0;
    parameter IS_ENBWREN_INVERTED = 1'b0;
    parameter IS_RSTRAMARSTRAM_INVERTED = 1'b0;
    parameter IS_RSTRAMB_INVERTED = 1'b0;
    parameter IS_RSTREGARSTREG_INVERTED = 1'b0;
    parameter IS_RSTREGB_INVERTED = 1'b0;

    specify
        // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/BRAM_L.sdf#L13
        $setup(ADDRARDADDR, posedge CLKARDCLK, 566);
        // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/BRAM_L.sdf#L17
        $setup(ADDRBWRADDR, posedge CLKBWRCLK, 566);
        // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/BRAM_L.sdf#L19
        $setup(WEA, posedge CLKARDCLK, 532);
        // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/BRAM_L.sdf#L21
        $setup(WEBWE, posedge CLKBWRCLK, 532);
        // https://github.com/SymbiFlow/prjxray-db/blob/4bc6385ab300b1819848371f508185f57b649a0e/artix7/timings/BRAM_L.sdf#L29
        $setup(REGCEAREGCE, posedge CLKARDCLK, 360);
        // https://github.com/SymbiFlow/prjxray-db/blob/4bc6385ab300b1819848371f508185f57b649a0e/artix7/timings/BRAM_L.sdf#L31
        $setup(RSTREGARSTREG, posedge CLKARDCLK, 342);
        // https://github.com/SymbiFlow/prjxray-db/blob/4bc6385ab300b1819848371f508185f57b649a0e/artix7/timings/BRAM_L.sdf#L49
        $setup(REGCEB, posedge CLKBWRCLK, 360);
        // https://github.com/SymbiFlow/prjxray-db/blob/4bc6385ab300b1819848371f508185f57b649a0e/artix7/timings/BRAM_L.sdf#L59
        $setup(RSTREGB, posedge CLKBWRCLK, 342);
        // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/BRAM_L.sdf#L123
        $setup(DIADI, posedge CLKARDCLK, 737);
        // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/BRAM_L.sdf#L133
        $setup(DIBDI, posedge CLKBWRCLK, 737);
        // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/BRAM_L.sdf#L125
        $setup(DIPADIP, posedge CLKARDCLK, 737);
        // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/BRAM_L.sdf#L135
        $setup(DIPBDIP, posedge CLKBWRCLK, 737);
        // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/BRAM_L.sdf#L143
        if (&DOA_REG) (posedge CLKARDCLK => (DOADO : 32'bx)) = 2454;
        // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/BRAM_L.sdf#L144
        if (&DOA_REG) (posedge CLKARDCLK => (DOPADOP : 4'bx)) = 2454;
        // https://github.com/SymbiFlow/prjxray-db/blob/4bc6385ab300b1819848371f508185f57b649a0e/artix7/timings/BRAM_L.sdf#L153
        if (|DOA_REG) (posedge CLKARDCLK => (DOADO : 32'bx)) = 882;
        // https://github.com/SymbiFlow/prjxray-db/blob/4bc6385ab300b1819848371f508185f57b649a0e/artix7/timings/BRAM_L.sdf#L154
        if (|DOA_REG) (posedge CLKARDCLK => (DOPADOP : 4'bx)) = 882;
        // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/BRAM_L.sdf#L163
        if (&DOB_REG) (posedge CLKBWRCLK => (DOBDO : 32'bx)) = 2454;
        // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/BRAM_L.sdf#L164
        if (&DOB_REG) (posedge CLKBWRCLK => (DOPBDOP : 4'bx)) = 2454;
        // https://github.com/SymbiFlow/prjxray-db/blob/4bc6385ab300b1819848371f508185f57b649a0e/artix7/timings/BRAM_L.sdf#L173
        if (|DOB_REG) (posedge CLKBWRCLK => (DOBDO : 32'bx)) = 882;
        // https://github.com/SymbiFlow/prjxray-db/blob/4bc6385ab300b1819848371f508185f57b649a0e/artix7/timings/BRAM_L.sdf#L174
        if (|DOB_REG) (posedge CLKBWRCLK => (DOPBDOP : 4'bx)) = 882;
    endspecify
endmodule
