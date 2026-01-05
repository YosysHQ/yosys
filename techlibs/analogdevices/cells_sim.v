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
`ifdef IS_T16FFC
  specify
    (I => O) = 42;
  endspecify
`endif
`ifdef IS_T40LP
  specify
    (I => O) = 121;
  endspecify
`endif
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
`ifdef IS_T16FFC
  specify
    (I => O) = 42;
  endspecify
`endif
`ifdef IS_T40LP
  specify
    (I => O) = 121;
  endspecify
`endif
endmodule

(* abc9_lut=1 *)
module LUT1(output O, input I0);
  parameter [1:0] INIT = 0;
  assign O = I0 ? INIT[1] : INIT[0];
`ifdef IS_T16FFC
  specify
    (I0 => O) = 42;
  endspecify
`endif
`ifdef IS_T40LP
  specify
    (I0 => O) = 121;
  endspecify
`endif
endmodule

(* abc9_lut=2 *)
module LUT2(output O, input I0, I1);
  parameter [3:0] INIT = 0;
  wire [ 1: 0] s1 = I1 ? INIT[ 3: 2] : INIT[ 1: 0];
  assign O = I0 ? s1[1] : s1[0];
`ifdef IS_T16FFC
  specify
    (I0 => O) = 42;
    (I1 => O) = 39;
  endspecify
`endif
`ifdef IS_T40LP
  specify
    (I0 => O) = 121;
    (I1 => O) = 121;
  endspecify
`endif
endmodule

(* abc9_lut=3 *)
module LUT3(output O, input I0, I1, I2);
  parameter [7:0] INIT = 0;
  wire [ 3: 0] s2 = I2 ? INIT[ 7: 4] : INIT[ 3: 0];
  wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
  assign O = I0 ? s1[1] : s1[0];
`ifdef IS_T16FFC
  specify
    (I0 => O) = 54;
    (I1 => O) = 51;
    (I2 => O) = 48;
  endspecify
`endif
`ifdef IS_T40LP
  specify
    (I0 => O) = 121;
    (I1 => O) = 121;
    (I2 => O) = 121;
  endspecify
`endif
endmodule

(* abc9_lut=4 *)
module LUT4(output O, input I0, I1, I2, I3);
  parameter [15:0] INIT = 0;
  wire [ 7: 0] s3 = I3 ? INIT[15: 8] : INIT[ 7: 0];
  wire [ 3: 0] s2 = I2 ?   s3[ 7: 4] :   s3[ 3: 0];
  wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
  assign O = I0 ? s1[1] : s1[0];
`ifdef IS_T16FFC
  specify
    (I0 => O) = 96;
    (I1 => O) = 87;
    (I2 => O) = 79;
    (I3 => O) = 71;
  endspecify
`endif
`ifdef IS_T40LP
  specify
    (I0 => O) = 121;
    (I1 => O) = 121;
    (I2 => O) = 121;
    (I3 => O) = 121;
  endspecify
`endif
endmodule

(* abc9_lut=5 *)
module LUT5(output O, input I0, I1, I2, I3, I4);
  parameter [31:0] INIT = 0;
  wire [15: 0] s4 = I4 ? INIT[31:16] : INIT[15: 0];
  wire [ 7: 0] s3 = I3 ?   s4[15: 8] :   s4[ 7: 0];
  wire [ 3: 0] s2 = I2 ?   s3[ 7: 4] :   s3[ 3: 0];
  wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
  assign O = I0 ? s1[1] : s1[0];
`ifdef IS_T16FFC
  specify
    (I0 => O) = 99;
    (I1 => O) = 90;
    (I2 => O) = 82;
    (I3 => O) = 74;
    (I4 => O) = 66;
  endspecify
`endif
`ifdef IS_T40LP
  specify
    (I0 => O) = 121;
    (I1 => O) = 121;
    (I2 => O) = 121;
    (I3 => O) = 121;
    (I4 => O) = 121;
  endspecify
`endif
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
`ifdef IS_T16FFC
  specify
    (I0 => O) = 42;
    (I1 => O) = 39;
    (I2 => O) = 36;
    (I3 => O) = 33;
    (I4 => O) = 30;
    (I5 => O) = 28;
  endspecify
`endif
`ifdef IS_T40LP
  specify
    (I0 => O) = 121;
    (I1 => O) = 121;
    (I2 => O) = 121;
    (I3 => O) = 121;
    (I4 => O) = 121;
    (I5 => O) = 121;
  endspecify
`endif
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
`ifdef IS_T16FFC
  specify
    (I0 => O) = 42 + 111 /* LUTMUX7.I1 */;
    (I1 => O) = 39 + 111 /* LUTMUX7.I1 */;
    (I2 => O) = 36 + 111 /* LUTMUX7.I1 */;
    (I3 => O) = 33 + 111 /* LUTMUX7.I1 */;
    (I4 => O) = 30 + 111 /* LUTMUX7.I1 */;
    (I5 => O) = 28 + 111 /* LUTMUX7.I1 */;
    (I6 => O) = 0  + 57  /* LUTMUX7.S */;
  endspecify
`endif
`ifdef IS_T40LP
  specify
    (I0 => O) = 121 + 140 /* LUTMUX7.I0 */;
    (I1 => O) = 121 + 140 /* LUTMUX7.I0 */;
    (I2 => O) = 121 + 140 /* LUTMUX7.I0 */;
    (I3 => O) = 121 + 140 /* LUTMUX7.I0 */;
    (I4 => O) = 121 + 140 /* LUTMUX7.I0 */;
    (I5 => O) = 121 + 140 /* LUTMUX7.I0 */;
    (I6 => O) = 0   + 162 /* LUTMUX7.S */;
  endspecify
`endif
`endif
endmodule

// This is a placeholder for ABC9 to extract the area/delay
//   cost of 3-input LUTs and is not intended to be instantiated
(* abc9_lut=24 *)
module \$__ABC9_LUT8 (output O, input I0, I1, I2, I3, I4, I5, I6, I7);
`ifndef __ICARUS__
`ifdef IS_T16FFC
  specify
    (I0 => O) = 42 + 111 /* LUTMUX7.I1 */ + 59 /* LUTMUX8.I0 */;
    (I1 => O) = 39 + 111 /* LUTMUX7.I1 */ + 59 /* LUTMUX8.I0 */;
    (I2 => O) = 36 + 111 /* LUTMUX7.I1 */ + 59 /* LUTMUX8.I0 */;
    (I3 => O) = 33 + 111 /* LUTMUX7.I1 */ + 59 /* LUTMUX8.I0 */;
    (I4 => O) = 30 + 111 /* LUTMUX7.I1 */ + 59 /* LUTMUX8.I0 */;
    (I5 => O) = 28 + 111 /* LUTMUX7.I1 */ + 59 /* LUTMUX8.I0 */;
    (I6 => O) = 0  +  57 /* LUTMUX7.S */  + 59 /* LUTMUX8.I0 */;
    (I7 => O) = 0  +  0                   + 60 /* LUTMUX8.S */;
  endspecify
`endif
`ifdef IS_T40LP
  specify
    (I0 => O) = 121 + 140 /* LUTMUX7.I0 */ + 146 /* LUTMUX8.I1 */;
    (I1 => O) = 121 + 140 /* LUTMUX7.I0 */ + 146 /* LUTMUX8.I1 */;
    (I2 => O) = 121 + 140 /* LUTMUX7.I0 */ + 146 /* LUTMUX8.I1 */;
    (I3 => O) = 121 + 140 /* LUTMUX7.I0 */ + 146 /* LUTMUX8.I1 */;
    (I4 => O) = 121 + 140 /* LUTMUX7.I0 */ + 146 /* LUTMUX8.I1 */;
    (I5 => O) = 121 + 140 /* LUTMUX7.I0 */ + 146 /* LUTMUX8.I1 */;
    (I6 => O) = 0   + 162 /* LUTMUX7.S */  + 146 /* LUTMUX8.I1 */;
    (I7 => O) = 0   +   0                  + 181 /* LUTMUX8.S */;
  endspecify
`endif
`endif
endmodule

(* abc9_box, lib_whitebox *)
module LUTMUX7(output O, input I0, I1, S);
  assign O = S ? I1 : I0;
`ifdef IS_T16FFC
  specify
    (I0 => O) = 95;
    (I1 => O) = 111;
    (S => O) = 57;
  endspecify
`endif
`ifdef IS_T40LP
  specify
    (I0 => O) = 140;
    (I1 => O) = 140;
    (S => O) = 162;
  endspecify
`endif
endmodule

(* abc9_box, lib_whitebox *)
module LUTMUX8(output O, input I0, I1, S);
  assign O = S ? I1 : I0;
`ifdef IS_T16FFC
  specify
    (I0 => O) = 59;
    (I1 => O) = 59;
    (S => O) = 60;
  endspecify
`endif
`ifdef IS_T40LP
  specify
    (I0 => O) = 140;
    (I1 => O) = 146;
    (S => O) = 181;
  endspecify
`endif
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
`ifdef IS_T16FFC
  specify
    (CI     => CO[0]) = 69;
    (DI[0]  => CO[0]) = 74;
    (S[0]   => CO[0]) = 76;

    (CI     => CO[1]) = 76;
    (DI[0]  => CO[1]) = 109;
    (DI[1]  => CO[1]) = 69;
    (S[0]   => CO[1]) = 99;
    (S[1]   => CO[1]) = 59;

    (CI     => CO[2]) = 144;
    (DI[0]  => CO[2]) = 155;
    (DI[1]  => CO[2]) = 126;
    (DI[2]  => CO[2]) = 63;
    (S[0]   => CO[2]) = 168;
    (S[1]   => CO[2]) = 117;
    (S[2]   => CO[2]) = 50;

    (CI     => CO[3]) = 20;
    (DI[0]  => CO[3]) = 167;
    (DI[1]  => CO[3]) = 181;
    (DI[2]  => CO[3]) = 173;
    (DI[3]  => CO[3]) = 77;
    (S[0]   => CO[3]) = 185;
    (S[1]   => CO[3]) = 182;
    (S[2]   => CO[3]) = 159;
    (S[3]   => CO[3]) = 179;

    (CI     => O[0]) = 50;
    (S[0]   => O[0]) = 82;

    (CI     => O[1]) = 61;
    (DI[0]  => O[1]) = 117;
    (S[0]   => O[1]) = 132;
    (S[1]   => O[1]) = 49;

    (CI     => O[2]) = 148;
    (DI[0]  => O[2]) = 196;
    (DI[1]  => O[2]) = 130;
    (S[0]   => O[2]) = 218;
    (S[1]   => O[2]) = 145;
    (S[2]   => O[2]) = 65;

    (CI     => O[3]) = 132;
    (DI[0]  => O[3]) = 208;
    (DI[1]  => O[3]) = 148;
    (DI[2]  => O[3]) = 110;
    (S[0]   => O[3]) = 204;
    (S[1]   => O[3]) = 160;
    (S[2]   => O[3]) = 97;
    (S[3]   => O[3]) = 39;

  endspecify
`endif
`ifdef IS_T40LP
  specify
    (S[0]   => O[0]) = 128;
    (CI     => O[0]) = 122;
    (DI[0]  => O[1]) = 268;
    (S[0]   => O[1]) = 256;
    (S[1]   => O[1]) = 141;
    (CI     => O[1]) = 173;
    (DI[0]  => O[2]) = 344;
    (DI[1]  => O[2]) = 320;
    (S[0]   => O[2]) = 271;
    (S[1]   => O[2]) = 225;
    (S[2]   => O[2]) = 129;
    (CI     => O[2]) = 223;
    (DI[0]  => O[3]) = 371;
    (DI[1]  => O[3]) = 383;
    (DI[2]  => O[3]) = 327;
    (S[0]   => O[3]) = 342;
    (S[1]   => O[3]) = 327;
    (S[2]   => O[3]) = 273;
    (S[3]   => O[3]) = 145;
    (CI     => O[3]) = 301;
    (DI[0]  => CO[0]) = 243;
    (S[0]   => CO[0]) = 136;
    (CI     => CO[0]) = 119;
    (DI[0]  => CO[1]) = 242;
    (DI[1]  => CO[1]) = 251;
    (S[0]   => CO[1]) = 220;
    (S[1]   => CO[1]) = 159;
    (CI     => CO[1]) = 155;
    (DI[0]  => CO[2]) = 275;
    (DI[1]  => CO[2]) = 241;
    (DI[2]  => CO[2]) = 231;
    (S[0]   => CO[2]) = 238;
    (S[1]   => CO[2]) = 197;
    (S[2]   => CO[2]) = 167;
    (CI     => CO[2]) = 197;
    (DI[0]  => CO[3]) = 294;
    (DI[1]  => CO[3]) = 303;
    (DI[2]  => CO[3]) = 317;
    (DI[3]  => CO[3]) = 205;
    (S[0]   => CO[3]) = 250;
    (S[1]   => CO[3]) = 292;
    (S[2]   => CO[3]) = 231;
    (S[3]   => CO[3]) = 178;
    (CI     => CO[3]) = 229;
  endspecify
`endif
endmodule

(* abc9_box, lib_whitebox *)
module CRY4INIT(
  (* abc9_carry *)
  output       CO,
  (* abc9_carry *)
  input        CYINIT
);
  assign CO = CYINIT;
`ifdef IS_T16FFC
  specify
    (CYINIT => CO) = 77;
  endspecify
`endif
`ifdef IS_T40LP
  specify
    (CYINIT => CO) = 205;
  endspecify
`endif
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
  initial Q = INIT;
  always @(posedge C) if (R) Q <= 1'b0; else if (CE) Q <= D;
`ifdef IS_T16FFC
  specify
    $setup(D , posedge C, 65);
    $setup(CE, posedge C, 63);
    $setup(R , posedge C, 63);
    if (R)        (posedge C => (Q : 1'b0)) = 291;
    if (!R && CE) (posedge C => (Q : D)) = 291;
  endspecify
`endif
`ifdef IS_T40LP
  specify
    $setup(D , posedge C, 119);
    $setup(CE, posedge C, 385);
    $setup(R , posedge C, 565);
    if (R)        (posedge C => (Q : 1'b0)) = 672;
    if (!R && CE) (posedge C => (Q : D)) = 672;
  endspecify
`endif
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
  initial Q = INIT;
  always @(negedge C) if (R) Q <= 1'b0; else if (CE) Q <= D;
`ifdef IS_T16FFC
  specify
    $setup(D , negedge C, 65);
    $setup(CE, negedge C, 63);
    $setup(R , negedge C, 63);
    if (R)        (negedge C => (Q : 1'b0)) = 291;
    if (!R && CE) (negedge C => (Q : D)) = 291;
  endspecify
`endif
`ifdef IS_T40LP
  specify
    $setup(D , negedge C, 119);
    $setup(CE, negedge C, 385);
    $setup(R , negedge C, 565);
    if (R)        (negedge C => (Q : 1'b0)) = 672;
    if (!R && CE) (negedge C => (Q : D)) = 672;
  endspecify
`endif
endmodule

(* abc9_flop, lib_whitebox *)
module FFSE (
  output reg Q,
  (* clkbuf_sink *)
  input C,
  input CE,
  input D,
  input S
);
  parameter [0:0] INIT = 1'b1;
  initial Q = INIT;
  always @(posedge C) if (S) Q <= 1'b1; else if (CE) Q <= D;
`ifdef IS_T16FFC
  specify
    $setup(D , posedge C, 65);
    $setup(CE, posedge C, 63);
    $setup(S , posedge C, 63);
    if (S)        (posedge C => (Q : 1'b1)) = 265;
    if (!S && CE) (posedge C => (Q : D)) = 265;
  endspecify
`endif
`ifdef IS_T40LP
  specify
    $setup(D , posedge C, 119);
    $setup(CE, posedge C, 385);
    $setup(S , posedge C, 565);
    if (S)        (posedge C => (Q : 1'b1)) = 672;
    if (!S && CE) (posedge C => (Q : D)) = 672;
  endspecify
`endif
endmodule

(* abc9_flop, lib_whitebox *)
module FFSE_N (
  output reg Q,
  (* clkbuf_sink *)
  input C,
  input CE,
  input D,
  input S
);
  parameter [0:0] INIT = 1'b1;
  initial Q = INIT;
  always @(negedge C) if (S) Q <= 1'b1; else if (CE) Q <= D;
`ifdef IS_T16FFC
  specify
    $setup(D , negedge C, 65);
    $setup(CE, negedge C, 63);
    $setup(S , negedge C, 63);
    if (S)        (negedge C => (Q : 1'b1)) = 265;
    if (!S && CE) (negedge C => (Q : D)) = 265;
  endspecify
`endif
`ifdef IS_T40LP
  specify
    $setup(D , negedge C, 119);
    $setup(CE, negedge C, 385);
    $setup(S , negedge C, 565);
    if (S)        (negedge C => (Q : 1'b1)) = 672;
    if (!S && CE) (negedge C => (Q : D)) = 672;
  endspecify
`endif
endmodule

(* abc9_box, lib_whitebox *)
module FFCE (
  output reg Q,
  (* clkbuf_sink *)
  input C,
  input CE,
  input CLR,
  input D
);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;
  always @(posedge C, posedge CLR) if ( CLR) Q <= 1'b0; else if (CE) Q <= D;
`ifdef IS_T16FFC
  specify
    $setup(D , posedge C, 65);
    $setup(CE, posedge C, 64);
    $setup(CLR, posedge C, 64);
    if (!CLR && CE) (posedge C => (Q : D)) = 192;
`ifdef YOSYS
    if (CLR) (CLR => Q) = 192;
`endif
  endspecify
`endif
`ifdef IS_T40LP
  specify
    $setup(D , posedge C, 119);
    $setup(CE, posedge C, 385);
    $setup(CLR, posedge C, 0 /* missing? */);
    if (!CLR && CE) (posedge C => (Q : D)) = 689;
`ifdef YOSYS
    if (CLR) (CLR => Q) = 0 /* missing? */;
`endif
  endspecify
`endif
endmodule

(* abc9_box, lib_whitebox *)
module FFCE_N (
  output reg Q,
  (* clkbuf_sink *)
  input C,
  input CE,
  input CLR,
  input D
);
  parameter [0:0] INIT = 1'b0;
  initial Q = INIT;
  always @(negedge C, posedge CLR) if (CLR) Q <= 1'b0; else if (CE) Q <= D;
`ifdef IS_T16FFC
  specify
    $setup(D,   negedge C, 65);
    $setup(CE,  negedge C, 64);
    $setup(CLR, negedge C, 64);
    if (!CLR && CE) (negedge C => (Q : D)) = 192;
`ifdef YOSYS
    if (CLR) (CLR => Q) = 192;
`endif
  endspecify
`endif
`ifdef IS_T40LP
  specify
    $setup(D,   negedge C, 119);
    $setup(CE,  negedge C, 385);
    $setup(CLR, negedge C, 0 /* missing? */);
    if (!CLR && CE) (negedge C => (Q : D)) = 689;
`ifdef YOSYS
    if (CLR) (CLR => Q) = 0 /* missing? */;
`endif
  endspecify
`endif
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
  initial Q = INIT;
  always @(posedge C, posedge PRE) if ( PRE) Q <= 1'b1; else if (CE) Q <= D;
`ifdef IS_T16FFC
  specify
    $setup(D,   posedge C, 65);
    $setup(CE,  posedge C, 65);
    $setup(PRE, posedge C, 65);
    if (!PRE && CE) (posedge C => (Q : D)) = 191;
`ifdef YOSYS
    if (PRE) (PRE => Q) = 191;
`endif
  endspecify
`endif
`ifdef IS_T40LP
  specify
    $setup(D,   posedge C, 119);
    $setup(CE,  posedge C, 385);
    $setup(PRE, posedge C, 0 /* missing? */);
    if (!PRE && CE) (posedge C => (Q : D)) = 672;
`ifdef YOSYS
    if (PRE) (PRE => Q) = 0 /* missing? */;
`endif
  endspecify
`endif
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
  initial Q = INIT;
  always @(negedge C, posedge PRE) if (PRE) Q <= 1'b1; else if (CE) Q <= D;
`ifdef IS_T16FFC
  specify
    $setup(D,   negedge C, 64);
    $setup(CE,  negedge C, 64);
    $setup(PRE, negedge C, 64);
    if (!PRE && CE) (negedge C => (Q : D)) = 291;
`ifdef YOSYS
    if (PRE) (PRE => Q) = 333;
`endif
  endspecify
`endif
`ifdef IS_T40LP
  specify
    $setup(D,   negedge C, 84);
    $setup(CE,  negedge C, 84);
    $setup(PRE, negedge C, 84);
    if (!PRE && CE) (negedge C => (Q : D)) = 712;
`ifdef YOSYS
    if (PRE) (PRE => Q) = 57;
`endif
  endspecify
`endif
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
`ifdef IS_T16FFC
  specify
    $setup(A0, posedge WCLK, 62);
    $setup(A1, posedge WCLK, 62);
    $setup(A2, posedge WCLK, 62);
    $setup(A3, posedge WCLK, 62);
    $setup(A4, posedge WCLK, 62);
    $setup(D,  posedge WCLK, 62);
    $setup(WE, posedge WCLK, 62);
    (A0 => O) = 100;
    (A1 => O) = 91;
    (A2 => O) = 83;
    (A3 => O) = 75;
    (A4 => O) = 67;
    (posedge WCLK => (O : D)) = 807;
  endspecify
`endif
`ifdef IS_T40LP
  specify
    $setup(A0, posedge WCLK, 84);
    $setup(A1, posedge WCLK, 84);
    $setup(A2, posedge WCLK, 84);
    $setup(A3, posedge WCLK, 84);
    $setup(A4, posedge WCLK, 84);
    $setup(D,  posedge WCLK, 84);
    $setup(WE, posedge WCLK, 84);
    (A0 => O) = 168;
    (A1 => O) = 168;
    (A2 => O) = 168;
    (A3 => O) = 168;
    (A4 => O) = 168;
    (posedge WCLK => (O : D)) = 1586;
  endspecify
`endif
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
`ifdef IS_T16FFC
  specify
    $setup(A0, posedge WCLK, 65);
    $setup(A1, posedge WCLK, 65);
    $setup(A2, posedge WCLK, 65);
    $setup(A3, posedge WCLK, 65);
    $setup(A4, posedge WCLK, 65);
    $setup(A5, posedge WCLK, 65);
    $setup(D,  posedge WCLK, 65);
    $setup(WE, posedge WCLK, 65);
    (A0 => O) = 184;
    (A1 => O) = 175;
    (A2 => O) = 167;
    (A3 => O) = 159;
    (A4 => O) = 151;
    (A5 => O) = 61;
    (posedge WCLK => (O : D)) = 747;
  endspecify
`endif
`ifdef IS_T40LP
  specify
    $setup(A0, posedge WCLK, 84);
    $setup(A1, posedge WCLK, 84);
    $setup(A2, posedge WCLK, 84);
    $setup(A3, posedge WCLK, 84);
    $setup(A4, posedge WCLK, 84);
    $setup(A5, posedge WCLK, 84);
    $setup(D,  posedge WCLK, 84);
    $setup(WE, posedge WCLK, 84);
    (A0 => O) = 466;
    (A1 => O) = 466;
    (A2 => O) = 466;
    (A3 => O) = 466;
    (A4 => O) = 466;
    (A5 => O) = 187;
    (posedge WCLK => (O : D)) = 1730;
  endspecify
`endif
endmodule

// Dual port.

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
  wire [4:0] dpra = {DPRA4, DPRA3, DPRA2, DPRA1, DPRA0};
  reg [31:0] mem = INIT;
  assign SPO = mem[a];
  assign DPO = mem[dpra];
  always @(posedge WCLK) if (WE) mem[a] <= D;
`ifdef IS_T16FFC
  specify
    $setup(A0, posedge WCLK, 62);
    $setup(A1, posedge WCLK, 62);
    $setup(A2, posedge WCLK, 62);
    $setup(A3, posedge WCLK, 62);
    $setup(A4, posedge WCLK, 62);
    $setup(D,  posedge WCLK, 62);
    $setup(WE, posedge WCLK, 62);
    (A0 => SPO) = 100;
    (A1 => SPO) = 91;
    (A2 => SPO) = 83;
    (A3 => SPO) = 75;
    (A4 => SPO) = 67;
    (DPRA0 => DPO) = 101;
    (DPRA1 => DPO) = 92;
    (DPRA2 => DPO) = 84;
    (DPRA3 => DPO) = 76;
    (DPRA4 => DPO) = 68;
    (posedge WCLK => (SPO : D)) = 807;
    (posedge WCLK => (DPO : D)) = 807;
  endspecify
`endif
`ifdef IS_T40LP
  specify
    // HACK: partial setup timing
    $setup(A0, posedge WCLK, 84);
    $setup(A1, posedge WCLK, 84);
    $setup(A2, posedge WCLK, 84);
    $setup(A3, posedge WCLK, 84);
    $setup(A4, posedge WCLK, 84);
    $setup(D,  posedge WCLK, 84);
    $setup(WE, posedge WCLK, 84);
    // HACK: No timing arcs for SPO; using ones for DPO
    // (are we meant to use the single-port timings here?)
    (A0 => SPO) = 142;
    (A1 => SPO) = 142;
    (A2 => SPO) = 142;
    (A3 => SPO) = 142;
    (A4 => SPO) = 142;
    (DPRA0 => DPO) = 142;
    (DPRA1 => DPO) = 142;
    (DPRA2 => DPO) = 142;
    (DPRA3 => DPO) = 142;
    (DPRA4 => DPO) = 142;
    (posedge WCLK => (SPO : D)) = 1586;
    (posedge WCLK => (DPO : D)) = 1586;
  endspecify
`endif
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
`ifdef IS_T16FFC
  specify
    $setup(A0, posedge WCLK, 65);
    $setup(A1, posedge WCLK, 65);
    $setup(A2, posedge WCLK, 65);
    $setup(A3, posedge WCLK, 65);
    $setup(A4, posedge WCLK, 65);
    $setup(A5, posedge WCLK, 65);
    $setup(D,  posedge WCLK, 65);
    $setup(WE, posedge WCLK, 65);
    (A0 => SPO) = 184;
    (A1 => SPO) = 175;
    (A2 => SPO) = 167;
    (A3 => SPO) = 159;
    (A4 => SPO) = 151;
    (A5 => SPO) = 61;
    (DPRA0 => DPO) = 164;
    (DPRA1 => DPO) = 155;
    (DPRA2 => DPO) = 147;
    (DPRA3 => DPO) = 139;
    (DPRA4 => DPO) = 131;
    (DPRA5 => DPO) = 64;    
    (posedge WCLK => (SPO : D)) = 761;
    (posedge WCLK => (DPO : D)) = 733;
  endspecify
`endif
`ifdef IS_T40LP
  specify
    // HACK: partial setup timing
    $setup(A0, posedge WCLK, 84);
    $setup(A1, posedge WCLK, 84);
    $setup(A2, posedge WCLK, 84);
    $setup(A3, posedge WCLK, 84);
    $setup(A4, posedge WCLK, 84);
    $setup(A5, posedge WCLK, 84);
    $setup(D,  posedge WCLK, 84);
    $setup(WE, posedge WCLK, 84);
    (A0 => SPO) = 466;
    (A1 => SPO) = 466;
    (A2 => SPO) = 466;
    (A3 => SPO) = 466;
    (A4 => SPO) = 466;
    (A5 => SPO) = 187;
    (DPRA0 => DPO) = 380;
    (DPRA1 => DPO) = 380;
    (DPRA2 => DPO) = 380;
    (DPRA3 => DPO) = 380;
    (DPRA4 => DPO) = 380;
    (DPRA5 => DPO) = 195;    
    (posedge WCLK => (SPO : D)) = 1730;
    (posedge WCLK => (DPO : D)) = 1799;
  endspecify
`endif
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

(* abc9_box *)
module RBBDSP (
  output [21:0] AO_LOC,
  output [21:0] BO_LOC,
  output        CE_O,
  output [1:0]  CO_LOC,
  output [47:0] DO_LOC,
  output [1:0]  OPCODE_O,
  output [47:0] P,
  output [47:0] PO_LOC,
  output        RST_O,

  input  [1:0]  CI_LOC,
  input  [1:0]  OPCODE,
  input  [1:0]  OPCODE_I,
  input  [21:0] A,
  input  [21:0] AI_LOC,
  input  [21:0] B,
  input  [21:0] BI_LOC,
  input  [47:0] D,
  input  [47:0] DI_LOC,
  input  [47:0] PI_LOC,
  input         CE,
  input         CE_I,
  (* clkbuf_sink *)
  input         CLK,
  input         CHIP_RST,
  input         RST_I,
  input         RST
);

parameter AI_SEL_IN = 1'b0;
parameter [1:0] BC_CI = 2'b00;
parameter BI_SEL = 1'b0;
parameter BI_SEL_IN = 1'b0;
parameter CE_A = 1'b0;
parameter CE_ADD = 1'b0;
parameter CE_B = 1'b0;
parameter CE_C = 1'b0;
parameter CE_CRY = 1'b0;
parameter [1:0] CE_D = 2'b0;
parameter CE_M = 1'b0;
parameter CE_OPCODE = 1'b0;
parameter CE_PADD = 1'b0;
parameter CE_RST = 1'b1;
parameter CE_SEL = 1'b0;
parameter CE_SFT = 1'b0;
parameter [3:0] CI_SEL = 4'b0011;
parameter DI_SEL = 1'b0;
parameter DI_SEL_IN = 1'b0;
parameter OPCODE_SEL = 1'b0;
parameter [9:0] OP_ADD = 10'b0;
parameter OP_CPLX = 1'b0;
parameter [1:0] OP_MULT = 2'b11;
parameter [9:0] OP_PADD = 10'b0;
parameter [5:0] OP_SFT = 6'b0;
parameter [3:0] OP_X = 4'b1010;
parameter [3:0] OP_Y = 4'b0101;
parameter [3:0] OP_Z = 4'b0000;
parameter PO_LOC_SEL = 1'b1;
parameter PO_NWK_SEL = 1'b1;
parameter REG_A = 1'b0;
parameter REG_ADD = 1'b0;
parameter REG_B = 1'b0;
parameter REG_C = 1'b0;
parameter REG_CRY = 1'b0;
parameter [1:0] REG_D = 2'b0;
parameter REG_M = 1'b0;
parameter REG_OPCODE = 1'b0;
parameter REG_PADD = 1'b0;
parameter REG_SFT = 1'b0;
parameter RST_SEL = 1'b0;
parameter FF_SYNC_RST = 1'b0;

specify
  if (!REG_A)    (A *> P) = 1000;
  if (!REG_B)    (B *> P) = 1000;
  if (!REG_D)    (D *> P) = 1000;
endspecify

// Much of this functionality is TODO.

assign P = $signed(A) * $signed(B);

endmodule

// Block RAM

module RBRAM #(
    parameter TARGET_NODE = "T40LP_Gen2.4",
    parameter BRAM_MODE = "SDP_1024x40",
    parameter QA_REG = 0,
    parameter QB_REG = 0,
    parameter CLKA_INV = 0,
    parameter CLKB_INV = 0,
    parameter DATA_WIDTH = 40,
    parameter ADDR_WIDTH = 12,
    parameter WE_WIDTH = 20,
    parameter PERR_WIDTH = 4
) (
    output [DATA_WIDTH-1:0] QA,
    input [DATA_WIDTH-1:0] DA,
    input CEA,
    input [WE_WIDTH-1:0] WEA,
    input [ADDR_WIDTH-1:0] AA,
    (* clkbuf_sink *)
    (* invertible_pin = "CLKA_INV" *)
    input CLKA,
    output [DATA_WIDTH-1:0] QB,
    input [DATA_WIDTH-1:0] DB,
    input CEB,
    input [WE_WIDTH-1:0] WEB,
    input [ADDR_WIDTH-1:0] AB,
    (* clkbuf_sink *)
    (* invertible_pin = "CLKB_INV" *)
    input CLKB,
    output reg [PERR_WIDTH-1:0] PERRA,
    output reg [PERR_WIDTH-1:0] PERRB,
    output SBEA,
    output SBEB,
    output MBEA,
    output MBEB,
    input SLP,
    input PD
);

endmodule

(* lib_whitebox *)
module RBRAM2 #(
    parameter TARGET_NODE = "T16FFC_Gen2.4",
    parameter BRAM_MODE = "SDP_2048x40",
    parameter QA_REG = 0,
    parameter QB_REG = 0,
    parameter CLKA_INV = 0,
    parameter CLKB_INV = 0,
    parameter DATA_WIDTH = 40,
    parameter ADDR_WIDTH = 13,
    parameter WE_WIDTH = 20,
    parameter PERR_WIDTH = 4
) (
    output [DATA_WIDTH-1:0] QA,
    input [DATA_WIDTH-1:0] DA,
    input CEA,
    input [WE_WIDTH-1:0] WEA,
    input [ADDR_WIDTH-1:0] AA,
    (* clkbuf_sink *)
    (* invertible_pin = "CLKA_INV" *)
    input CLKA,
    output [DATA_WIDTH-1:0] QB,
    input [DATA_WIDTH-1:0] DB,
    input CEB,
    input [WE_WIDTH-1:0] WEB,
    input [ADDR_WIDTH-1:0] AB,
    (* clkbuf_sink *)
    (* invertible_pin = "CLKB_INV" *)
    input CLKB,
    output reg [PERR_WIDTH-1:0] PERRA,
    output reg [PERR_WIDTH-1:0] PERRB,
    output SBEA,
    output SBEB,
    output MBEA,
    output MBEB,
    input SLP,
    input PD
);

// Timings simplified for now
specify
  $setup(DA,  posedge CLKA, 2440);
  $setup(CEA, posedge CLKA, 1668);
  $setup(AA,  posedge CLKA, 2289);

  $setup(DB,  posedge CLKB, 2420);
  $setup(CEB, posedge CLKB, 1805);
  $setup(AB,  posedge CLKB, 2170);

  (posedge CLKA => (QA : DA)) = 2227;
  (posedge CLKB => (QB : DB)) = 2189;
endspecify

endmodule
