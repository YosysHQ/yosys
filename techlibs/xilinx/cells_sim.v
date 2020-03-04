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

module IBUF(
    output O,
    (* iopad_external_pin *)
    input I);
  parameter IOSTANDARD = "default";
  parameter IBUF_LOW_PWR = 0;
  assign O = I;
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

module OBUF(
    (* iopad_external_pin *)
    output O,
    input I);
  parameter IOSTANDARD = "default";
  parameter DRIVE = 12;
  parameter SLEW = "SLOW";
  assign O = I;
endmodule

module IOBUF (
    (* iopad_external_pin *)
    inout IO,
    output O,
    input I,
    input T
);
    parameter integer DRIVE = 12;
    parameter IBUF_LOW_PWR = "TRUE";
    parameter IOSTANDARD = "DEFAULT";
    parameter SLEW = "SLOW";
    assign IO = T ? 1'bz : I;
    assign O = IO;
endmodule

module OBUFT (
    (* iopad_external_pin *)
    output O,
    input I,
    input T
);
    parameter CAPACITANCE = "DONT_CARE";
    parameter integer DRIVE = 12;
    parameter IOSTANDARD = "DEFAULT";
    parameter SLEW = "SLOW";
    assign O = T ? 1'bz : I;
endmodule

module BUFG(
    (* clkbuf_driver *)
    output O,
    input I);

  assign O = I;
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

// module OBUFT(output O, input I, T);
//   assign O = T ? 1'bz : I;
// endmodule

// module IOBUF(inout IO, output O, input I, T);
//   assign O = IO, IO = T ? 1'bz : I;
// endmodule

module INV(
    (* clkbuf_inv = "I" *)
    output O,
    input I
);
  assign O = !I;
  specify
    (I => O) = 127;
  endspecify
endmodule

(* abc9_lut=1 *)
module LUT1(output O, input I0);
  parameter [1:0] INIT = 0;
  assign O = I0 ? INIT[1] : INIT[0];
  specify
    (I0 => O) = 127;
  endspecify
endmodule

(* abc9_lut=2 *)
module LUT2(output O, input I0, I1);
  parameter [3:0] INIT = 0;
  wire [ 1: 0] s1 = I1 ? INIT[ 3: 2] : INIT[ 1: 0];
  assign O = I0 ? s1[1] : s1[0];
  specify
    (I0 => O) = 238;
    (I1 => O) = 127;
  endspecify
endmodule

(* abc9_lut=3 *)
module LUT3(output O, input I0, I1, I2);
  parameter [7:0] INIT = 0;
  wire [ 3: 0] s2 = I2 ? INIT[ 7: 4] : INIT[ 3: 0];
  wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
  assign O = I0 ? s1[1] : s1[0];
  specify
    (I0 => O) = 407;
    (I1 => O) = 238;
    (I2 => O) = 127;
  endspecify
endmodule

(* abc9_lut=3 *)
module LUT4(output O, input I0, I1, I2, I3);
  parameter [15:0] INIT = 0;
  wire [ 7: 0] s3 = I3 ? INIT[15: 8] : INIT[ 7: 0];
  wire [ 3: 0] s2 = I2 ?   s3[ 7: 4] :   s3[ 3: 0];
  wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
  assign O = I0 ? s1[1] : s1[0];
  specify
    (I0 => O) = 472;
    (I1 => O) = 407;
    (I2 => O) = 238;
    (I3 => O) = 127;
  endspecify
endmodule

(* abc9_lut=3 *)
module LUT5(output O, input I0, I1, I2, I3, I4);
  parameter [31:0] INIT = 0;
  wire [15: 0] s4 = I4 ? INIT[31:16] : INIT[15: 0];
  wire [ 7: 0] s3 = I3 ?   s4[15: 8] :   s4[ 7: 0];
  wire [ 3: 0] s2 = I2 ?   s3[ 7: 4] :   s3[ 3: 0];
  wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
  assign O = I0 ? s1[1] : s1[0];
  specify
    (I0 => O) = 631;
    (I1 => O) = 472;
    (I2 => O) = 407;
    (I3 => O) = 238;
    (I4 => O) = 127;
  endspecify
endmodule

// This is a placeholder for ABC9 to extract the area/delay
//   cost of 3-input LUTs and is not intended to be instantiated

(* abc9_lut=5 *)
module LUT6(output O, input I0, I1, I2, I3, I4, I5);
  parameter [63:0] INIT = 0;
  wire [31: 0] s5 = I5 ? INIT[63:32] : INIT[31: 0];
  wire [15: 0] s4 = I4 ?   s5[31:16] :   s5[15: 0];
  wire [ 7: 0] s3 = I3 ?   s4[15: 8] :   s4[ 7: 0];
  wire [ 3: 0] s2 = I2 ?   s3[ 7: 4] :   s3[ 3: 0];
  wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
  assign O = I0 ? s1[1] : s1[0];
  specify
    (I0 => O) = 642;
    (I1 => O) = 631;
    (I2 => O) = 472;
    (I3 => O) = 407;
    (I4 => O) = 238;
    (I5 => O) = 127;
  endspecify
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

// This is a placeholder for ABC9 to extract the area/delay
//   cost of 3-input LUTs and is not intended to be instantiated
(* abc9_lut=10 *)
module \$__ABC9_LUT7 (output O, input I0, I1, I2, I3, I4, I5, I6);
`ifndef __ICARUS__
  specify
                                                 // https://github.com/SymbiFlow/prjxray-db/blob/1c85daf1b115da4d27ca83c6b89f53a94de39748/artix7/timings/slicel.sdf#L867
    (I0 => O) = 642 + 223 /* to cross F7BMUX */ + 174 /* CMUX */;
    (I1 => O) = 631 + 223 /* to cross F7BMUX */ + 174 /* CMUX */;
    (I2 => O) = 472 + 223 /* to cross F7BMUX */ + 174 /* CMUX */;
    (I3 => O) = 407 + 223 /* to cross F7BMUX */ + 174 /* CMUX */;
    (I4 => O) = 238 + 223 /* to cross F7BMUX */ + 174 /* CMUX */;
    (I5 => O) = 127 + 223 /* to cross F7BMUX */ + 174 /* CMUX */;
    (I6 => O) = 0 + 296 /* to select F7BMUX */ + 174 /* CMUX */;
  endspecify
`endif
endmodule

// This is a placeholder for ABC9 to extract the area/delay
//   cost of 3-input LUTs and is not intended to be instantiated
(* abc9_lut=20 *)
module \$__ABC9_LUT8 (output O, input I0, I1, I2, I3, I4, I5, I6, I7);
`ifndef __ICARUS__
  specify
                                                                             // https://github.com/SymbiFlow/prjxray-db/blob/1c85daf1b115da4d27ca83c6b89f53a94de39748/artix7/timings/slicel.sdf#L716
    (I0 => O) = 642 + 223 /* to cross F7BMUX */ + 104 /* to cross F8MUX */ + 192 /* BMUX */;
    (I1 => O) = 631 + 223 /* to cross F7BMUX */ + 104 /* to cross F8MUX */ + 192 /* BMUX */;
    (I2 => O) = 472 + 223 /* to cross F7BMUX */ + 104 /* to cross F8MUX */ + 192 /* BMUX */;
    (I3 => O) = 407 + 223 /* to cross F7BMUX */ + 104 /* to cross F8MUX */ + 192 /* BMUX */;
    (I4 => O) = 238 + 223 /* to cross F7BMUX */ + 104 /* to cross F8MUX */ + 192 /* BMUX */;
    (I5 => O) = 127 + 223 /* to cross F7BMUX */ + 104 /* to cross F8MUX */ + 192 /* BMUX */;
    (I6 => O) = 0 + 296 /* to select F7BMUX */  + 104 /* to cross F8MUX */ + 192 /* BMUX */;
    (I7 => O) = 0 + 0 + 273 /* to select F8MUX */ + 192 /* BMUX */;
  endspecify
`endif
endmodule

module MUXCY(output O, input CI, DI, S);
  assign O = S ? CI : DI;
endmodule

module MUXF5(output O, input I0, I1, S);
  assign O = S ? I1 : I0;
endmodule

module MUXF6(output O, input I0, I1, S);
  assign O = S ? I1 : I0;
endmodule

(* abc9_box, lib_whitebox *)
module MUXF7(output O, input I0, I1, S);
  assign O = S ? I1 : I0;
  specify
    // https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLL_L.sdf#L451-L453
    (I0 => O) = 217;
    (I1 => O) = 223;
    (S => O) = 296;
  endspecify
endmodule

(* abc9_box, lib_whitebox *)
module MUXF8(output O, input I0, I1, S);
  assign O = S ? I1 : I0;
  specify
    // Max delays from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLL_L.sdf#L462-L464
    (I0 => O) = 104;
    (I1 => O) = 94;
    (S => O) = 273;
  endspecify
endmodule

module MUXF9(output O, input I0, I1, S);
  assign O = S ? I1 : I0;
endmodule

module XORCY(output O, input CI, LI);
  assign O = CI ^ LI;
endmodule

(* abc9_box, lib_whitebox *)
module CARRY4(
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
    (CYINIT => O[0]) = 482;
    (S[0]   => O[0]) = 223;
    (CI     => O[0]) = 222;
    (CYINIT => O[1]) = 598;
    (DI[0]  => O[1]) = 407;
    (S[0]   => O[1]) = 400;
    (S[1]   => O[1]) = 205;
    (CI     => O[1]) = 334;
    (CYINIT => O[2]) = 584;
    (DI[0]  => O[2]) = 556;
    (DI[1]  => O[2]) = 537;
    (S[0]   => O[2]) = 523;
    (S[1]   => O[2]) = 558;
    (S[2]   => O[2]) = 226;
    (CI     => O[2]) = 239;
    (CYINIT => O[3]) = 642;
    (DI[0]  => O[3]) = 615;
    (DI[1]  => O[3]) = 596;
    (DI[2]  => O[3]) = 438;
    (S[0]   => O[3]) = 582;
    (S[1]   => O[3]) = 618;
    (S[2]   => O[3]) = 330;
    (S[3]   => O[3]) = 227;
    (CI     => O[3]) = 313;
    (CYINIT => CO[0]) = 536;
    (DI[0]  => CO[0]) = 379;
    (S[0]   => CO[0]) = 340;
    (CI     => CO[0]) = 271;
    (CYINIT => CO[1]) = 494;
    (DI[0]  => CO[1]) = 465;
    (DI[1]  => CO[1]) = 445;
    (S[0]   => CO[1]) = 433;
    (S[1]   => CO[1]) = 469;
    (CI     => CO[1]) = 157;
    (CYINIT => CO[2]) = 592;
    (DI[0]  => CO[2]) = 540;
    (DI[1]  => CO[2]) = 520;
    (DI[2]  => CO[2]) = 356;
    (S[0]   => CO[2]) = 512;
    (S[1]   => CO[2]) = 548;
    (S[2]   => CO[2]) = 292;
    (CI     => CO[2]) = 228;
    (CYINIT => CO[3]) = 580;
    (DI[0]  => CO[3]) = 526;
    (DI[1]  => CO[3]) = 507;
    (DI[2]  => CO[3]) = 398;
    (DI[3]  => CO[3]) = 385;
    (S[0]   => CO[3]) = 508;
    (S[1]   => CO[3]) = 528;
    (S[2]   => CO[3]) = 378;
    (S[3]   => CO[3]) = 380;
    (CI     => CO[3]) = 114;
  endspecify
endmodule

module CARRY8(
  output [7:0] CO,
  output [7:0] O,
  input        CI,
  input        CI_TOP,
  input  [7:0] DI, S
);
  parameter CARRY_TYPE = "SINGLE_CY8";
  wire CI4 = (CARRY_TYPE == "DUAL_CY4" ? CI_TOP : CO[3]);
  assign O = S ^ {CO[6:4], CI4, CO[2:0], CI};
  assign CO[0] = S[0] ? CI : DI[0];
  assign CO[1] = S[1] ? CO[0] : DI[1];
  assign CO[2] = S[2] ? CO[1] : DI[2];
  assign CO[3] = S[3] ? CO[2] : DI[3];
  assign CO[4] = S[4] ? CI4 : DI[4];
  assign CO[5] = S[5] ? CO[4] : DI[5];
  assign CO[6] = S[6] ? CO[5] : DI[6];
  assign CO[7] = S[7] ? CO[6] : DI[7];
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

module ORCY (output O, input CI, I);
  assign O = CI | I;
endmodule

module MULT_AND (output LO, input I0, I1);
  assign LO = I0 & I1;
endmodule

// Flip-flops and latches.

// Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLL_L.sdf#L238-L250

(* abc9_flop, lib_whitebox *)
module FDRE (
  output reg Q,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_C_INVERTED" *)
  input C,
  input CE,
  (* invertible_pin = "IS_D_INVERTED" *)
  input D,
  (* invertible_pin = "IS_R_INVERTED" *)
  input R
);
  parameter [0:0] INIT = 1'b0;
  parameter [0:0] IS_C_INVERTED = 1'b0;
  parameter [0:0] IS_D_INVERTED = 1'b0;
  parameter [0:0] IS_R_INVERTED = 1'b0;
  initial Q <= INIT;
  generate
  case (|IS_C_INVERTED)
    1'b0: always @(posedge C) if (R == !IS_R_INVERTED) Q <= 1'b0; else if (CE) Q <= D ^ IS_D_INVERTED;
    1'b1: always @(negedge C) if (R == !IS_R_INVERTED) Q <= 1'b0; else if (CE) Q <= D ^ IS_D_INVERTED;
  endcase
  endgenerate
  specify
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L249
    //$setup(D , posedge C &&& CE && !IS_C_INVERTED , -46); // Negative times not currently supported
    //$setup(D , negedge C &&& CE &&  IS_C_INVERTED , -46); // Negative times not currently supported
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L248
    $setup(CE, posedge C &&& !IS_C_INVERTED, 109);
    $setup(CE, negedge C &&&  IS_C_INVERTED, 109);
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L274
    $setup(R , posedge C &&& !IS_C_INVERTED, 404);
    $setup(R , negedge C &&&  IS_C_INVERTED, 404);
    // https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLL_L.sdf#L243
    if (!IS_C_INVERTED && R ^ IS_R_INVERTED)        (posedge C => (Q : 1'b0)) = 303;
    if ( IS_C_INVERTED && R ^ IS_R_INVERTED)        (negedge C => (Q : 1'b0)) = 303;
    if (!IS_C_INVERTED && R ~^ IS_R_INVERTED && CE) (posedge C => (Q : D ^ IS_D_INVERTED)) = 303;
    if ( IS_C_INVERTED && R ~^ IS_R_INVERTED && CE) (negedge C => (Q : D ^ IS_D_INVERTED)) = 303;
  endspecify
endmodule

(* abc9_flop, lib_whitebox *)
module FDRE_1 (
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
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L249
    //$setup(D , negedge C &&& CE, -46); // Negative times not currently supported
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L248
    $setup(CE, negedge C, 109);
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L274
    $setup(R , negedge C, 404);    // https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLL_L.sdf#L243
    if (R)        (negedge C => (Q : 1'b0)) = 303;
    if (!R && CE) (negedge C => (Q : D)) = 303;
  endspecify
endmodule

(* abc9_flop, lib_whitebox *)
module FDSE (
  output reg Q,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_C_INVERTED" *)
  input C,
  input CE,
  (* invertible_pin = "IS_D_INVERTED" *)
  input D,
  (* invertible_pin = "IS_S_INVERTED" *)
  input S
);
  parameter [0:0] INIT = 1'b1;
  parameter [0:0] IS_C_INVERTED = 1'b0;
  parameter [0:0] IS_D_INVERTED = 1'b0;
  parameter [0:0] IS_S_INVERTED = 1'b0;
  initial Q <= INIT;
  generate
  case (|IS_C_INVERTED)
    1'b0: always @(posedge C) if (S == !IS_S_INVERTED) Q <= 1'b1; else if (CE) Q <= D ^ IS_D_INVERTED;
    1'b1: always @(negedge C) if (S == !IS_S_INVERTED) Q <= 1'b1; else if (CE) Q <= D ^ IS_D_INVERTED;
  endcase
  endgenerate
  specify
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L249
    //$setup(D , posedge C &&& !IS_C_INVERTED && CE, -46); // Negative times not currently supported
    //$setup(D , negedge C &&&  IS_C_INVERTED && CE, -46); // Negative times not currently supported
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L248
    $setup(CE, posedge C &&& !IS_C_INVERTED, 109);
    $setup(CE, negedge C &&&  IS_C_INVERTED, 109);
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L274
    $setup(S , posedge C &&& !IS_C_INVERTED, 404);
    $setup(S , negedge C &&&  IS_C_INVERTED, 404);
    // https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLL_L.sdf#L243
    if (!IS_C_INVERTED && S ^ IS_S_INVERTED)        (posedge C => (Q : 1'b1)) = 303;
    if ( IS_C_INVERTED && S ^ IS_S_INVERTED)        (negedge C => (Q : 1'b1)) = 303;
    if (!IS_C_INVERTED && S ~^ IS_S_INVERTED && CE) (posedge C => (Q : D ^ IS_D_INVERTED)) = 303;
    if ( IS_C_INVERTED && S ~^ IS_S_INVERTED && CE) (negedge C => (Q : D ^ IS_D_INVERTED)) = 303;
  endspecify
endmodule

(* abc9_flop, lib_whitebox *)
module FDSE_1 (
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
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L249
    //$setup(D , negedge C &&& CE, -46); // Negative times not currently supported
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L248
    $setup(CE, negedge C, 109);
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L274
    $setup(S , negedge C, 404);
    // https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLL_L.sdf#L243
    if (S)        (negedge C => (Q : 1'b1)) = 303;
    if (!S && CE) (negedge C => (Q : D)) = 303;
  endspecify
endmodule

module FDRSE (
  output reg Q,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_C_INVERTED" *)
  input C,
  (* invertible_pin = "IS_CE_INVERTED" *)
  input CE,
  (* invertible_pin = "IS_D_INVERTED" *)
  input D,
  (* invertible_pin = "IS_R_INVERTED" *)
  input R,
  (* invertible_pin = "IS_S_INVERTED" *)
  input S
);
  parameter [0:0] INIT = 1'b0;
  parameter [0:0] IS_C_INVERTED = 1'b0;
  parameter [0:0] IS_CE_INVERTED = 1'b0;
  parameter [0:0] IS_D_INVERTED = 1'b0;
  parameter [0:0] IS_R_INVERTED = 1'b0;
  parameter [0:0] IS_S_INVERTED = 1'b0;
  initial Q <= INIT;
  wire c = C ^ IS_C_INVERTED;
  wire ce = CE ^ IS_CE_INVERTED;
  wire d = D ^ IS_D_INVERTED;
  wire r = R ^ IS_R_INVERTED;
  wire s = S ^ IS_S_INVERTED;
  always @(posedge c)
    if (r)
      Q <= 0;
    else if (s)
      Q <= 1;
    else if (ce)
      Q <= d;
endmodule

(* abc9_flop, lib_whitebox *)
module FDCE (
  output reg Q,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_C_INVERTED" *)
  input C,
  input CE,
  (* invertible_pin = "IS_CLR_INVERTED" *)
  input CLR,
  (* invertible_pin = "IS_D_INVERTED" *)
  input D
);
  parameter [0:0] INIT = 1'b0;
  parameter [0:0] IS_C_INVERTED = 1'b0;
  parameter [0:0] IS_D_INVERTED = 1'b0;
  parameter [0:0] IS_CLR_INVERTED = 1'b0;
  initial Q <= INIT;
  generate
  case ({|IS_C_INVERTED, |IS_CLR_INVERTED})
    2'b00: always @(posedge C, posedge CLR) if ( CLR) Q <= 1'b0; else if (CE) Q <= D ^ IS_D_INVERTED;
    2'b01: always @(posedge C, negedge CLR) if (!CLR) Q <= 1'b0; else if (CE) Q <= D ^ IS_D_INVERTED;
    2'b10: always @(negedge C, posedge CLR) if ( CLR) Q <= 1'b0; else if (CE) Q <= D ^ IS_D_INVERTED;
    2'b11: always @(negedge C, negedge CLR) if (!CLR) Q <= 1'b0; else if (CE) Q <= D ^ IS_D_INVERTED;
  endcase
  endgenerate
  specify
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L249
    //$setup(D , posedge C &&& !IS_C_INVERTED && CE, -46); // Negative times not currently supported
    //$setup(D , negedge C &&&  IS_C_INVERTED && CE, -46); // Negative times not currently supported
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L248
    $setup(CE , posedge C &&& !IS_C_INVERTED, 109);
    $setup(CE , negedge C &&&  IS_C_INVERTED, 109);
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L274
    $setup(CLR, posedge C &&& !IS_C_INVERTED, 404);
    $setup(CLR, negedge C &&&  IS_C_INVERTED, 404);
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L270
    //if (!IS_CLR_INVERTED) (posedge CLR => (Q : 1'b0)) = 764; // Captured by $__ABC9_ASYNC0
    //if ( IS_CLR_INVERTED) (negedge CLR => (Q : 1'b0)) = 764; // Captured by $__ABC9_ASYNC0
    if (!IS_C_INVERTED && CLR ~^ IS_CLR_INVERTED && CE) (posedge C => (Q : D ^ IS_D_INVERTED)) = 303;
    if ( IS_C_INVERTED && CLR ~^ IS_CLR_INVERTED && CE) (negedge C => (Q : D ^ IS_D_INVERTED)) = 303;
  endspecify
endmodule

(* abc9_flop, lib_whitebox *)
module FDCE_1 (
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
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L249
    //$setup(D , negedge C &&& CE, -46); // Negative times not currently supported
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L248
    $setup(CE , negedge C, 109);
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L274
    $setup(CLR, negedge C, 404);
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L270
    //(posedge CLR => (Q : 1'b0)) = 764; // Captured by $__ABC9_ASYNC0
    if (!CLR && CE) (negedge C => (Q : D)) = 303;
  endspecify
endmodule

(* abc9_flop, lib_whitebox *)
module FDPE (
  output reg Q,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_C_INVERTED" *)
  input C,
  input CE,
  (* invertible_pin = "IS_D_INVERTED" *)
  input D,
  (* invertible_pin = "IS_PRE_INVERTED" *)
  input PRE
);
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
  endcase
  endgenerate
  specify
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L249
    //$setup(D , posedge C &&& !IS_C_INVERTED && CE, -46); // Negative times not currently supported
    //$setup(D , negedge C &&&  IS_C_INVERTED && CE, -46); // Negative times not currently supported
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L248
    $setup(CE , posedge C &&& !IS_C_INVERTED, 109);
    $setup(CE , negedge C &&&  IS_C_INVERTED, 109);
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L274
    $setup(PRE, posedge C &&& !IS_C_INVERTED, 404);
    $setup(PRE, negedge C &&&  IS_C_INVERTED, 404);
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L270
    //if (!IS_PRE_INVERTED) (posedge PRE => (Q : 1'b1)) = 764; // Captured by $__ABC9_ASYNC1
    //if ( IS_PRE_INVERTED) (negedge PRE => (Q : 1'b1)) = 764; // Captured by $__ABC9_ASYNC1
    if (!IS_C_INVERTED && PRE ~^ IS_PRE_INVERTED && CE) (posedge C => (Q : D ^ IS_D_INVERTED)) = 303;
    if ( IS_C_INVERTED && PRE ~^ IS_PRE_INVERTED && CE) (negedge C => (Q : D ^ IS_D_INVERTED)) = 303;
  endspecify
endmodule

(* abc9_flop, lib_whitebox *)
module FDPE_1 (
  output reg Q,
  (* clkbuf_sink *)
  input C,
  input CE,
  input D,
  input PRE
);
  parameter [0:0] INIT = 1'b1;
  initial Q <= INIT;
  always @(negedge C, posedge PRE) if (PRE) Q <= 1'b1; else if (CE) Q <= D;
  specify
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L249
    //$setup(D , negedge C &&& CE, -46); // Negative times not currently supported
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L248
    $setup(CE , negedge C, 109);
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L274
    $setup(PRE, negedge C, 404);
    // https://github.com/SymbiFlow/prjxray-db/blob/23c8b0851f979f0799318eaca90174413a46b257/artix7/timings/slicel.sdf#L270
    //if (!IS_PRE_INVERTED) (posedge PRE => (Q : 1'b1)) = 764; // Captured by $__ABC9_ASYNC1
    //if (IS_PRE_INVERTED)  (negedge PRE => (Q : 1'b1)) = 764; // Captured by $__ABC9_ASYNC1
    if (!PRE && CE) (negedge C => (Q : D)) = 303;
  endspecify
endmodule

module FDCPE (
  output wire Q,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_C_INVERTED" *)
  input C,
  input CE,
  (* invertible_pin = "IS_CLR_INVERTED" *)
  input CLR,
  input D,
  (* invertible_pin = "IS_PRE_INVERTED" *)
  input PRE
);
  parameter [0:0] INIT = 1'b0;
  parameter [0:0] IS_C_INVERTED = 1'b0;
  parameter [0:0] IS_CLR_INVERTED = 1'b0;
  parameter [0:0] IS_PRE_INVERTED = 1'b0;
  wire c = C ^ IS_C_INVERTED;
  wire clr = CLR ^ IS_CLR_INVERTED;
  wire pre = PRE ^ IS_PRE_INVERTED;
  // Hacky model to avoid simulation-synthesis mismatches.
  reg qc, qp, qs;
  initial qc = INIT;
  initial qp = INIT;
  initial qs = 0;
  always @(posedge c, posedge clr) begin
    if (clr)
      qc <= 0;
    else if (CE)
      qc <= D;
  end
  always @(posedge c, posedge pre) begin
    if (pre)
      qp <= 1;
    else if (CE)
      qp <= D;
  end
  always @* begin
    if (clr)
      qs <= 0;
    else if (pre)
      qs <= 1;
  end
  assign Q = qs ? qp : qc;
endmodule

module LDCE (
  output reg Q,
  (* invertible_pin = "IS_CLR_INVERTED" *)
  input CLR,
  input D,
  (* invertible_pin = "IS_G_INVERTED" *)
  input G,
  input GE
);
  parameter [0:0] INIT = 1'b0;
  parameter [0:0] IS_CLR_INVERTED = 1'b0;
  parameter [0:0] IS_G_INVERTED = 1'b0;
  parameter MSGON = "TRUE";
  parameter XON = "TRUE";
  initial Q = INIT;
  wire clr = CLR ^ IS_CLR_INVERTED;
  wire g = G ^ IS_G_INVERTED;
  always @*
    if (clr) Q <= 1'b0;
    else if (GE && g) Q <= D;
endmodule

module LDPE (
  output reg Q,
  input D,
  (* invertible_pin = "IS_G_INVERTED" *)
  input G,
  input GE,
  (* invertible_pin = "IS_PRE_INVERTED" *)
  input PRE
);
  parameter [0:0] INIT = 1'b1;
  parameter [0:0] IS_G_INVERTED = 1'b0;
  parameter [0:0] IS_PRE_INVERTED = 1'b0;
  parameter MSGON = "TRUE";
  parameter XON = "TRUE";
  initial Q = INIT;
  wire g = G ^ IS_G_INVERTED;
  wire pre = PRE ^ IS_PRE_INVERTED;
  always @*
    if (pre) Q <= 1'b1;
    else if (GE && g) Q <= D;
endmodule

module LDCPE (
  output reg Q,
  (* invertible_pin = "IS_CLR_INVERTED" *)
  input CLR,
  (* invertible_pin = "IS_D_INVERTED" *)
  input D,
  (* invertible_pin = "IS_G_INVERTED" *)
  input G,
  (* invertible_pin = "IS_GE_INVERTED" *)
  input GE,
  (* invertible_pin = "IS_PRE_INVERTED" *)
  input PRE
);
  parameter [0:0] INIT = 1'b1;
  parameter [0:0] IS_CLR_INVERTED = 1'b0;
  parameter [0:0] IS_D_INVERTED = 1'b0;
  parameter [0:0] IS_G_INVERTED = 1'b0;
  parameter [0:0] IS_GE_INVERTED = 1'b0;
  parameter [0:0] IS_PRE_INVERTED = 1'b0;
  initial Q = INIT;
  wire d = D ^ IS_D_INVERTED;
  wire g = G ^ IS_G_INVERTED;
  wire ge = GE ^ IS_GE_INVERTED;
  wire clr = CLR ^ IS_CLR_INVERTED;
  wire pre = PRE ^ IS_PRE_INVERTED;
  always @*
    if (clr) Q <= 1'b0;
    else if (pre) Q <= 1'b1;
    else if (ge && g) Q <= d;
endmodule

module AND2B1L (
  output O,
  input DI,
  (* invertible_pin = "IS_SRI_INVERTED" *)
  input SRI
);
  parameter [0:0] IS_SRI_INVERTED = 1'b0;
  assign O = DI & ~(SRI ^ IS_SRI_INVERTED);
endmodule

module OR2L (
  output O,
  input DI,
  (* invertible_pin = "IS_SRI_INVERTED" *)
  input SRI
);
  parameter [0:0] IS_SRI_INVERTED = 1'b0;
  assign O = DI | (SRI ^ IS_SRI_INVERTED);
endmodule

// LUTRAM.

// Single port.

module RAM16X1S (
  output O,
  input A0, A1, A2, A3,
  input D,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input WCLK,
  input WE
);
  parameter [15:0] INIT = 16'h0000;
  parameter [0:0] IS_WCLK_INVERTED = 1'b0;
  wire [3:0] a = {A3, A2, A1, A0};
  reg [15:0] mem = INIT;
  assign O = mem[a];
  wire clk = WCLK ^ IS_WCLK_INVERTED;
  always @(posedge clk) if (WE) mem[a] <= D;
endmodule

module RAM16X1S_1 (
  output O,
  input A0, A1, A2, A3,
  input D,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input WCLK,
  input WE
);
  parameter [15:0] INIT = 16'h0000;
  parameter [0:0] IS_WCLK_INVERTED = 1'b0;
  wire [3:0] a = {A3, A2, A1, A0};
  reg [15:0] mem = INIT;
  assign O = mem[a];
  wire clk = WCLK ^ IS_WCLK_INVERTED;
  always @(negedge clk) if (WE) mem[a] <= D;
endmodule

module RAM32X1S (
  output O,
  input A0, A1, A2, A3, A4,
  input D,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input WCLK,
  input WE
);
  parameter [31:0] INIT = 32'h00000000;
  parameter [0:0] IS_WCLK_INVERTED = 1'b0;
  wire [4:0] a = {A4, A3, A2, A1, A0};
  reg [31:0] mem = INIT;
  assign O = mem[a];
  wire clk = WCLK ^ IS_WCLK_INVERTED;
  always @(posedge clk) if (WE) mem[a] <= D;
endmodule

module RAM32X1S_1 (
  output O,
  input A0, A1, A2, A3, A4,
  input D,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input WCLK,
  input WE
);
  parameter [31:0] INIT = 32'h00000000;
  parameter [0:0] IS_WCLK_INVERTED = 1'b0;
  wire [4:0] a = {A4, A3, A2, A1, A0};
  reg [31:0] mem = INIT;
  assign O = mem[a];
  wire clk = WCLK ^ IS_WCLK_INVERTED;
  always @(negedge clk) if (WE) mem[a] <= D;
endmodule

module RAM64X1S (
  output O,
  input A0, A1, A2, A3, A4, A5,
  input D,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input WCLK,
  input WE
);
  parameter [63:0] INIT = 64'h0000000000000000;
  parameter [0:0] IS_WCLK_INVERTED = 1'b0;
  wire [5:0] a = {A5, A4, A3, A2, A1, A0};
  reg [63:0] mem = INIT;
  assign O = mem[a];
  wire clk = WCLK ^ IS_WCLK_INVERTED;
  always @(posedge clk) if (WE) mem[a] <= D;
endmodule

module RAM64X1S_1 (
  output O,
  input A0, A1, A2, A3, A4, A5,
  input D,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input WCLK,
  input WE
);
  parameter [63:0] INIT = 64'h0000000000000000;
  parameter [0:0] IS_WCLK_INVERTED = 1'b0;
  wire [5:0] a = {A5, A4, A3, A2, A1, A0};
  reg [63:0] mem = INIT;
  assign O = mem[a];
  wire clk = WCLK ^ IS_WCLK_INVERTED;
  always @(negedge clk) if (WE) mem[a] <= D;
endmodule

module RAM128X1S (
  output O,
  input A0, A1, A2, A3, A4, A5, A6,
  input D,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input WCLK,
  input WE
);
  parameter [127:0] INIT = 128'h00000000000000000000000000000000;
  parameter [0:0] IS_WCLK_INVERTED = 1'b0;
  wire [6:0] a = {A6, A5, A4, A3, A2, A1, A0};
  reg [127:0] mem = INIT;
  assign O = mem[a];
  wire clk = WCLK ^ IS_WCLK_INVERTED;
  always @(posedge clk) if (WE) mem[a] <= D;
endmodule

module RAM128X1S_1 (
  output O,
  input A0, A1, A2, A3, A4, A5, A6,
  input D,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input WCLK,
  input WE
);
  parameter [127:0] INIT = 128'h00000000000000000000000000000000;
  parameter [0:0] IS_WCLK_INVERTED = 1'b0;
  wire [6:0] a = {A6, A5, A4, A3, A2, A1, A0};
  reg [127:0] mem = INIT;
  assign O = mem[a];
  wire clk = WCLK ^ IS_WCLK_INVERTED;
  always @(negedge clk) if (WE) mem[a] <= D;
endmodule

module RAM256X1S (
  output O,
  input [7:0] A,
  input D,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input WCLK,
  input WE
);
  parameter [255:0] INIT = 256'h0;
  parameter [0:0] IS_WCLK_INVERTED = 1'b0;
  reg [255:0] mem = INIT;
  assign O = mem[A];
  wire clk = WCLK ^ IS_WCLK_INVERTED;
  always @(posedge clk) if (WE) mem[A] <= D;
endmodule

module RAM512X1S (
  output O,
  input [8:0] A,
  input D,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input WCLK,
  input WE
);
  parameter [511:0] INIT = 512'h0;
  parameter [0:0] IS_WCLK_INVERTED = 1'b0;
  reg [511:0] mem = INIT;
  assign O = mem[A];
  wire clk = WCLK ^ IS_WCLK_INVERTED;
  always @(posedge clk) if (WE) mem[A] <= D;
endmodule

// Single port, wide.

module RAM16X2S (
  output O0, O1,
  input A0, A1, A2, A3,
  input D0, D1,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input WCLK,
  input WE
);
  parameter [15:0] INIT_00 = 16'h0000;
  parameter [15:0] INIT_01 = 16'h0000;
  parameter [0:0] IS_WCLK_INVERTED = 1'b0;
  wire [3:0] a = {A3, A2, A1, A0};
  wire clk = WCLK ^ IS_WCLK_INVERTED;
  reg [15:0] mem0 = INIT_00;
  reg [15:0] mem1 = INIT_01;
  assign O0 = mem0[a];
  assign O1 = mem1[a];
  always @(posedge clk)
    if (WE) begin
      mem0[a] <= D0;
      mem1[a] <= D1;
    end
endmodule

module RAM32X2S (
  output O0, O1,
  input A0, A1, A2, A3, A4,
  input D0, D1,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input WCLK,
  input WE
);
  parameter [31:0] INIT_00 = 32'h00000000;
  parameter [31:0] INIT_01 = 32'h00000000;
  parameter [0:0] IS_WCLK_INVERTED = 1'b0;
  wire [4:0] a = {A4, A3, A2, A1, A0};
  wire clk = WCLK ^ IS_WCLK_INVERTED;
  reg [31:0] mem0 = INIT_00;
  reg [31:0] mem1 = INIT_01;
  assign O0 = mem0[a];
  assign O1 = mem1[a];
  always @(posedge clk)
    if (WE) begin
      mem0[a] <= D0;
      mem1[a] <= D1;
    end
endmodule

module RAM64X2S (
  output O0, O1,
  input A0, A1, A2, A3, A4, A5,
  input D0, D1,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input WCLK,
  input WE
);
  parameter [63:0] INIT_00 = 64'h0000000000000000;
  parameter [63:0] INIT_01 = 64'h0000000000000000;
  parameter [0:0] IS_WCLK_INVERTED = 1'b0;
  wire [5:0] a = {A5, A3, A2, A1, A0};
  wire clk = WCLK ^ IS_WCLK_INVERTED;
  reg [63:0] mem0 = INIT_00;
  reg [63:0] mem1 = INIT_01;
  assign O0 = mem0[a];
  assign O1 = mem1[a];
  always @(posedge clk)
    if (WE) begin
      mem0[a] <= D0;
      mem1[a] <= D1;
    end
endmodule

module RAM16X4S (
  output O0, O1, O2, O3,
  input A0, A1, A2, A3,
  input D0, D1, D2, D3,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input WCLK,
  input WE
);
  parameter [15:0] INIT_00 = 16'h0000;
  parameter [15:0] INIT_01 = 16'h0000;
  parameter [15:0] INIT_02 = 16'h0000;
  parameter [15:0] INIT_03 = 16'h0000;
  parameter [0:0] IS_WCLK_INVERTED = 1'b0;
  wire [3:0] a = {A3, A2, A1, A0};
  wire clk = WCLK ^ IS_WCLK_INVERTED;
  reg [15:0] mem0 = INIT_00;
  reg [15:0] mem1 = INIT_01;
  reg [15:0] mem2 = INIT_02;
  reg [15:0] mem3 = INIT_03;
  assign O0 = mem0[a];
  assign O1 = mem1[a];
  assign O2 = mem2[a];
  assign O3 = mem3[a];
  always @(posedge clk)
    if (WE) begin
      mem0[a] <= D0;
      mem1[a] <= D1;
      mem2[a] <= D2;
      mem3[a] <= D3;
    end
endmodule

module RAM32X4S (
  output O0, O1, O2, O3,
  input A0, A1, A2, A3, A4,
  input D0, D1, D2, D3,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input WCLK,
  input WE
);
  parameter [31:0] INIT_00 = 32'h00000000;
  parameter [31:0] INIT_01 = 32'h00000000;
  parameter [31:0] INIT_02 = 32'h00000000;
  parameter [31:0] INIT_03 = 32'h00000000;
  parameter [0:0] IS_WCLK_INVERTED = 1'b0;
  wire [4:0] a = {A4, A3, A2, A1, A0};
  wire clk = WCLK ^ IS_WCLK_INVERTED;
  reg [31:0] mem0 = INIT_00;
  reg [31:0] mem1 = INIT_01;
  reg [31:0] mem2 = INIT_02;
  reg [31:0] mem3 = INIT_03;
  assign O0 = mem0[a];
  assign O1 = mem1[a];
  assign O2 = mem2[a];
  assign O3 = mem3[a];
  always @(posedge clk)
    if (WE) begin
      mem0[a] <= D0;
      mem1[a] <= D1;
      mem2[a] <= D2;
      mem3[a] <= D3;
    end
endmodule

module RAM16X8S (
  output [7:0] O,
  input A0, A1, A2, A3,
  input [7:0] D,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input WCLK,
  input WE
);
  parameter [15:0] INIT_00 = 16'h0000;
  parameter [15:0] INIT_01 = 16'h0000;
  parameter [15:0] INIT_02 = 16'h0000;
  parameter [15:0] INIT_03 = 16'h0000;
  parameter [15:0] INIT_04 = 16'h0000;
  parameter [15:0] INIT_05 = 16'h0000;
  parameter [15:0] INIT_06 = 16'h0000;
  parameter [15:0] INIT_07 = 16'h0000;
  parameter [0:0] IS_WCLK_INVERTED = 1'b0;
  wire [3:0] a = {A3, A2, A1, A0};
  wire clk = WCLK ^ IS_WCLK_INVERTED;
  reg [15:0] mem0 = INIT_00;
  reg [15:0] mem1 = INIT_01;
  reg [15:0] mem2 = INIT_02;
  reg [15:0] mem3 = INIT_03;
  reg [15:0] mem4 = INIT_04;
  reg [15:0] mem5 = INIT_05;
  reg [15:0] mem6 = INIT_06;
  reg [15:0] mem7 = INIT_07;
  assign O[0] = mem0[a];
  assign O[1] = mem1[a];
  assign O[2] = mem2[a];
  assign O[3] = mem3[a];
  assign O[4] = mem4[a];
  assign O[5] = mem5[a];
  assign O[6] = mem6[a];
  assign O[7] = mem7[a];
  always @(posedge clk)
    if (WE) begin
      mem0[a] <= D[0];
      mem1[a] <= D[1];
      mem2[a] <= D[2];
      mem3[a] <= D[3];
      mem4[a] <= D[4];
      mem5[a] <= D[5];
      mem6[a] <= D[6];
      mem7[a] <= D[7];
    end
endmodule

module RAM32X8S (
  output [7:0] O,
  input A0, A1, A2, A3, A4,
  input [7:0] D,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input WCLK,
  input WE
);
  parameter [31:0] INIT_00 = 32'h00000000;
  parameter [31:0] INIT_01 = 32'h00000000;
  parameter [31:0] INIT_02 = 32'h00000000;
  parameter [31:0] INIT_03 = 32'h00000000;
  parameter [31:0] INIT_04 = 32'h00000000;
  parameter [31:0] INIT_05 = 32'h00000000;
  parameter [31:0] INIT_06 = 32'h00000000;
  parameter [31:0] INIT_07 = 32'h00000000;
  parameter [0:0] IS_WCLK_INVERTED = 1'b0;
  wire [4:0] a = {A4, A3, A2, A1, A0};
  wire clk = WCLK ^ IS_WCLK_INVERTED;
  reg [31:0] mem0 = INIT_00;
  reg [31:0] mem1 = INIT_01;
  reg [31:0] mem2 = INIT_02;
  reg [31:0] mem3 = INIT_03;
  reg [31:0] mem4 = INIT_04;
  reg [31:0] mem5 = INIT_05;
  reg [31:0] mem6 = INIT_06;
  reg [31:0] mem7 = INIT_07;
  assign O[0] = mem0[a];
  assign O[1] = mem1[a];
  assign O[2] = mem2[a];
  assign O[3] = mem3[a];
  assign O[4] = mem4[a];
  assign O[5] = mem5[a];
  assign O[6] = mem6[a];
  assign O[7] = mem7[a];
  always @(posedge clk)
    if (WE) begin
      mem0[a] <= D[0];
      mem1[a] <= D[1];
      mem2[a] <= D[2];
      mem3[a] <= D[3];
      mem4[a] <= D[4];
      mem5[a] <= D[5];
      mem6[a] <= D[6];
      mem7[a] <= D[7];
    end
endmodule

// Dual port.

module RAM16X1D (
  output DPO, SPO,
  input  D,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input  WCLK,
  input  WE,
  input  A0, A1, A2, A3,
  input  DPRA0, DPRA1, DPRA2, DPRA3
);
  parameter INIT = 16'h0;
  parameter IS_WCLK_INVERTED = 1'b0;
  wire [3:0] a = {A3, A2, A1, A0};
  wire [3:0] dpra = {DPRA3, DPRA2, DPRA1, DPRA0};
  reg [15:0] mem = INIT;
  assign SPO = mem[a];
  assign DPO = mem[dpra];
  wire clk = WCLK ^ IS_WCLK_INVERTED;
  always @(posedge clk) if (WE) mem[a] <= D;
endmodule

module RAM16X1D_1 (
  output DPO, SPO,
  input  D,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input  WCLK,
  input  WE,
  input  A0, A1, A2, A3,
  input  DPRA0, DPRA1, DPRA2, DPRA3
);
  parameter INIT = 16'h0;
  parameter IS_WCLK_INVERTED = 1'b0;
  wire [3:0] a = {A3, A2, A1, A0};
  wire [3:0] dpra = {DPRA3, DPRA2, DPRA1, DPRA0};
  reg [15:0] mem = INIT;
  assign SPO = mem[a];
  assign DPO = mem[dpra];
  wire clk = WCLK ^ IS_WCLK_INVERTED;
  always @(negedge clk) if (WE) mem[a] <= D;
endmodule

module RAM32X1D (
  output DPO, SPO,
  input  D,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input  WCLK,
  input  WE,
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
  specify
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L986
    $setup(D , posedge WCLK &&& !IS_WCLK_INVERTED && WE, 453);
    $setup(D , negedge WCLK &&&  IS_WCLK_INVERTED && WE, 453);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L834
    $setup(WE, posedge WCLK &&& !IS_WCLK_INVERTED, 654);
    $setup(WE, negedge WCLK &&&  IS_WCLK_INVERTED, 654);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L800
    $setup(A0, posedge WCLK &&& !IS_WCLK_INVERTED && WE, 245);
    $setup(A0, negedge WCLK &&&  IS_WCLK_INVERTED && WE, 245);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L798
    $setup(A1, posedge WCLK &&& !IS_WCLK_INVERTED && WE, 208);
    $setup(A1, negedge WCLK &&&  IS_WCLK_INVERTED && WE, 208);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L796
    $setup(A2, posedge WCLK &&& !IS_WCLK_INVERTED && WE, 147);
    $setup(A2, negedge WCLK &&&  IS_WCLK_INVERTED && WE, 147);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L794
    $setup(A3, posedge WCLK &&& !IS_WCLK_INVERTED && WE, 68);
    $setup(A3, negedge WCLK &&&  IS_WCLK_INVERTED && WE, 68);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L792
    $setup(A4, posedge WCLK &&& !IS_WCLK_INVERTED && WE, 66);
    $setup(A4, posedge WCLK &&&  IS_WCLK_INVERTED && WE, 66);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L981
    if (!IS_WCLK_INVERTED) (posedge WCLK => (SPO : D))    = 1153;
    if (!IS_WCLK_INVERTED) (posedge WCLK => (DPO : 1'bx)) = 1153;
    if ( IS_WCLK_INVERTED) (posedge WCLK => (SPO : D))    = 1153;
    if ( IS_WCLK_INVERTED) (negedge WCLK => (DPO : 1'bx)) = 1153;
    // Captured by $__ABC9_RAM6
    //({A0,DPRA0} => {SPO,DPO}) = 642;
    //({A1,DPRA1} => {SPO,DPO}) = 631;
    //({A2,DPRA2} => {SPO,DPO}) = 472;
    //({A3,DPRA3} => {SPO,DPO}) = 407;
    //({A4,DPRA4} => {SPO,DPO}) = 238;
  endspecify
endmodule

module RAM32X1D_1 (
  output DPO, SPO,
  input  D,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input  WCLK,
  input  WE,
  input  A0,
  input  A1,
  input  A2,
  input  A3,
  input  A4,
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
  always @(negedge clk) if (WE) mem[a] <= D;
  specify
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L986
    $setup(D , negedge WCLK &&& WE, 453);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L834
    $setup(WE, negedge WCLK, 654);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L800
    $setup(A0, negedge WCLK &&& WE, 245);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L798
    $setup(A1, negedge WCLK &&& WE, 208);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L796
    $setup(A2, negedge WCLK &&& WE, 147);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L794
    $setup(A3, negedge WCLK &&& WE, 68);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L792
    $setup(A4, negedge WCLK &&& WE, 66);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L981
    if (WE) (negedge WCLK => (SPO : D))    = 1153;
    if (WE) (negedge WCLK => (DPO : 1'bx)) = 1153;
    // Captured by $__ABC9_RAM6
    //({A0,DPRA0} => {SPO,DPO}) = 642;
    //({A1,DPRA1} => {SPO,DPO}) = 631;
    //({A2,DPRA2} => {SPO,DPO}) = 472;
    //({A3,DPRA3} => {SPO,DPO}) = 407;
    //({A4,DPRA4} => {SPO,DPO}) = 238;
  endspecify
endmodule

module RAM64X1D (
  output DPO, SPO,
  input  D,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input  WCLK,
  input  WE,
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
  specify
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L986
    $setup(D , posedge WCLK &&& !IS_WCLK_INVERTED && WE, 453);
    $setup(D , negedge WCLK &&&  IS_WCLK_INVERTED && WE, 453);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L834
    $setup(WE, posedge WCLK &&& !IS_WCLK_INVERTED, 654);
    $setup(WE, negedge WCLK &&&  IS_WCLK_INVERTED, 654);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L828
    $setup(A0, posedge WCLK &&& !IS_WCLK_INVERTED && WE, 362);
    $setup(A0, negedge WCLK &&&  IS_WCLK_INVERTED && WE, 362);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L826
    $setup(A1, posedge WCLK &&& !IS_WCLK_INVERTED && WE, 245);
    $setup(A1, negedge WCLK &&&  IS_WCLK_INVERTED && WE, 245);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L824
    $setup(A2, posedge WCLK &&& !IS_WCLK_INVERTED && WE, 208);
    $setup(A2, negedge WCLK &&&  IS_WCLK_INVERTED && WE, 208);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L822
    $setup(A3, posedge WCLK &&& !IS_WCLK_INVERTED && WE, 147);
    $setup(A3, negedge WCLK &&&  IS_WCLK_INVERTED && WE, 147);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L820
    $setup(A4, posedge WCLK &&& !IS_WCLK_INVERTED && WE, 68);
    $setup(A4, negedge WCLK &&&  IS_WCLK_INVERTED && WE, 68);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L818
    $setup(A5, posedge WCLK &&& !IS_WCLK_INVERTED && WE, 66);
    $setup(A5, negedge WCLK &&&  IS_WCLK_INVERTED && WE, 66);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L981
    if (!IS_WCLK_INVERTED && WE) (posedge WCLK => (SPO : D))    = 1153;
    if (!IS_WCLK_INVERTED && WE) (posedge WCLK => (DPO : 1'bx)) = 1153;
    if ( IS_WCLK_INVERTED && WE) (negedge WCLK => (SPO : D))    = 1153;
    if ( IS_WCLK_INVERTED && WE) (negedge WCLK => (DPO : 1'bx)) = 1153;
    // Captured by $__ABC9_RAM6
    //({A0,DPRA0} => {SPO,DPO}) = 642;
    //({A1,DPRA1} => {SPO,DPO}) = 631;
    //({A2,DPRA2} => {SPO,DPO}) = 472;
    //({A3,DPRA3} => {SPO,DPO}) = 407;
    //({A4,DPRA4} => {SPO,DPO}) = 238;
    //({A5,DPRA5} => {SPO,DPO}) = 127;
  endspecify
endmodule

module RAM64X1D_1 (
  output DPO, SPO,
  input  D,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input  WCLK,
  input  WE,
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
  always @(negedge clk) if (WE) mem[a] <= D;
  specify
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L986
    $setup(D , negedge WCLK &&& WE, 453);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L834
    $setup(WE, negedge WCLK, 654);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L828
    $setup(A0, negedge WCLK &&& WE, 362);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L826
    $setup(A1, negedge WCLK &&& WE, 245);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L824
    $setup(A2, negedge WCLK &&& WE, 208);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L822
    $setup(A3, negedge WCLK &&& WE, 147);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L820
    $setup(A4, negedge WCLK &&& WE, 68);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L818
    $setup(A5, negedge WCLK &&& WE, 66);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L981
    if (WE) (negedge WCLK => (SPO : D))    = 1153;
    if (WE) (negedge WCLK => (DPO : 1'bx)) = 1153;
  endspecify
endmodule

module RAM128X1D (
  output       DPO, SPO,
  input        D,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input        WCLK,
  input        WE,
  input  [6:0] A,
  input  [6:0] DPRA
);
  parameter INIT = 128'h0;
  parameter IS_WCLK_INVERTED = 1'b0;
  reg [127:0] mem = INIT;
  assign SPO = mem[A];
  assign DPO = mem[DPRA];
  wire clk = WCLK ^ IS_WCLK_INVERTED;
  always @(posedge clk) if (WE) mem[A] <= D;
  specify
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L986
    $setup(D , posedge WCLK &&& !IS_WCLK_INVERTED && WE, 453);
    $setup(D , negedge WCLK &&&  IS_WCLK_INVERTED && WE, 453);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L834
    $setup(WE, posedge WCLK &&& !IS_WCLK_INVERTED, 654);
    $setup(WE, negedge WCLK &&&  IS_WCLK_INVERTED, 654);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L818-830
    $setup(A[0], posedge WCLK &&& !IS_WCLK_INVERTED && WE, 616);
    $setup(A[0], negedge WCLK &&&  IS_WCLK_INVERTED && WE, 616);
    $setup(A[1], posedge WCLK &&& !IS_WCLK_INVERTED && WE, 362);
    $setup(A[1], negedge WCLK &&&  IS_WCLK_INVERTED && WE, 362);
    $setup(A[2], posedge WCLK &&& !IS_WCLK_INVERTED && WE, 245);
    $setup(A[2], negedge WCLK &&&  IS_WCLK_INVERTED && WE, 245);
    $setup(A[3], posedge WCLK &&& !IS_WCLK_INVERTED && WE, 208);
    $setup(A[3], negedge WCLK &&&  IS_WCLK_INVERTED && WE, 208);
    $setup(A[4], posedge WCLK &&& !IS_WCLK_INVERTED && WE, 147);
    $setup(A[4], negedge WCLK &&&  IS_WCLK_INVERTED && WE, 147);
    $setup(A[5], posedge WCLK &&& !IS_WCLK_INVERTED && WE, 68);
    $setup(A[5], negedge WCLK &&&  IS_WCLK_INVERTED && WE, 68);
    $setup(A[6], posedge WCLK &&& !IS_WCLK_INVERTED && WE, 66);
    $setup(A[6], negedge WCLK &&&  IS_WCLK_INVERTED && WE, 66);
`ifndef __ICARUS__
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L981
    if (!IS_WCLK_INVERTED && WE) (posedge WCLK => (SPO : D))    = 1153 + 217 /* to cross F7AMUX */ + 175 /* AMUX */;
    if ( IS_WCLK_INVERTED && WE) (negedge WCLK => (DPO : 1'bx)) = 1153 + 223 /* to cross F7BMUX */ + 174 /* CMUX */;
`endif
    // Captured by $__ABC9_RAM7
    //(A[0] => SPO) = 642 + 193 /* to cross F7AMUX */ + 175 /* AMUX */;
    //(A[1] => SPO) = 631 + 193 /* to cross F7AMUX */ + 175 /* AMUX */;
    //(A[2] => SPO) = 472 + 193 /* to cross F7AMUX */ + 175 /* AMUX */;
    //(A[3] => SPO) = 407 + 193 /* to cross F7AMUX */ + 175 /* AMUX */;
    //(A[4] => SPO) = 238 + 193 /* to cross F7AMUX */ + 175 /* AMUX */;
    //(A[5] => SPO) = 127 + 193 /* to cross F7AMUX */ + 175 /* AMUX */;
    //(A[6] => SPO) = 0 + 276 /* to select F7AMUX */ + 175 /* AMUX */;
    //(DPRA[0] => DPO) = 642 + 223 /* to cross MUXF7 */ + 174 /* CMUX */;
    //(DPRA[1] => DPO) = 631 + 223 /* to cross MUXF7 */ + 174 /* CMUX */;
    //(DPRA[2] => DPO) = 472 + 223 /* to cross MUXF7 */ + 174 /* CMUX */;
    //(DPRA[3] => DPO) = 407 + 223 /* to cross MUXF7 */ + 174 /* CMUX */;
    //(DPRA[4] => DPO) = 238 + 223 /* to cross MUXF7 */ + 174 /* CMUX */;
    //(DPRA[5] => DPO) = 127 + 223 /* to cross MUXF7 */ + 174 /* CMUX */;
    //(DPRA[6] => DPO) = 0 + 296 /* to select MUXF7 */ + 174 /* CMUX */;
  endspecify
endmodule

module RAM256X1D (
  output DPO, SPO,
  input        D,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input        WCLK,
  input        WE,
  input  [7:0] A, DPRA
);
  parameter INIT = 256'h0;
  parameter IS_WCLK_INVERTED = 1'b0;
  reg [255:0] mem = INIT;
  assign SPO = mem[A];
  assign DPO = mem[DPRA];
  wire clk = WCLK ^ IS_WCLK_INVERTED;
  always @(posedge clk) if (WE) mem[A] <= D;
endmodule

// Multi port.

module RAM32M (
  output [1:0] DOA,
  output [1:0] DOB,
  output [1:0] DOC,
  output [1:0] DOD,
  input  [4:0] ADDRA, ADDRB, ADDRC,
  input  [4:0] ADDRD,
  input  [1:0] DIA,
  input  [1:0] DIB,
  input  [1:0] DIC,
  input  [1:0] DID,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input        WCLK,
  input        WE
);
  parameter [63:0] INIT_A = 64'h0000000000000000;
  parameter [63:0] INIT_B = 64'h0000000000000000;
  parameter [63:0] INIT_C = 64'h0000000000000000;
  parameter [63:0] INIT_D = 64'h0000000000000000;
  parameter [0:0] IS_WCLK_INVERTED = 1'b0;
  reg [63:0] mem_a = INIT_A;
  reg [63:0] mem_b = INIT_B;
  reg [63:0] mem_c = INIT_C;
  reg [63:0] mem_d = INIT_D;
  assign DOA = mem_a[2*ADDRA+:2];
  assign DOB = mem_b[2*ADDRB+:2];
  assign DOC = mem_c[2*ADDRC+:2];
  assign DOD = mem_d[2*ADDRD+:2];
  wire clk = WCLK ^ IS_WCLK_INVERTED;
  always @(posedge clk)
    if (WE) begin
      mem_a[2*ADDRD+:2] <= DIA;
      mem_b[2*ADDRD+:2] <= DIB;
      mem_c[2*ADDRD+:2] <= DIC;
      mem_d[2*ADDRD+:2] <= DID;
    end
  specify
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L986
    $setup(ADDRD[0], posedge WCLK &&& !IS_WCLK_INVERTED && WE, 245);
    $setup(ADDRD[0], negedge WCLK &&&  IS_WCLK_INVERTED && WE, 245);
    $setup(ADDRD[1], posedge WCLK &&& !IS_WCLK_INVERTED && WE, 208);
    $setup(ADDRD[1], negedge WCLK &&&  IS_WCLK_INVERTED && WE, 208);
    $setup(ADDRD[2], posedge WCLK &&& !IS_WCLK_INVERTED && WE, 147);
    $setup(ADDRD[2], negedge WCLK &&&  IS_WCLK_INVERTED && WE, 147);
    $setup(ADDRD[3], posedge WCLK &&& !IS_WCLK_INVERTED && WE, 68);
    $setup(ADDRD[3], negedge WCLK &&&  IS_WCLK_INVERTED && WE, 68);
    $setup(ADDRD[4], posedge WCLK &&& !IS_WCLK_INVERTED && WE, 66);
    $setup(ADDRD[4], negedge WCLK &&&  IS_WCLK_INVERTED && WE, 66);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L986-L988
    $setup(DIA[0], posedge WCLK &&& !IS_WCLK_INVERTED && WE, 453);
    $setup(DIA[0], negedge WCLK &&&  IS_WCLK_INVERTED && WE, 453);
    $setup(DIA[1], posedge WCLK &&& !IS_WCLK_INVERTED && WE, 384);
    $setup(DIA[1], negedge WCLK &&&  IS_WCLK_INVERTED && WE, 384);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L1054-L1056
    $setup(DIB[0], posedge WCLK &&& !IS_WCLK_INVERTED && WE, 461);
    $setup(DIB[0], negedge WCLK &&&  IS_WCLK_INVERTED && WE, 461);
    $setup(DIB[1], posedge WCLK &&& !IS_WCLK_INVERTED && WE, 354);
    $setup(DIB[1], negedge WCLK &&&  IS_WCLK_INVERTED && WE, 354);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L1122-L1124
    $setup(DIC[0], posedge WCLK &&& !IS_WCLK_INVERTED && WE, 457);
    $setup(DIC[0], negedge WCLK &&&  IS_WCLK_INVERTED && WE, 457);
    $setup(DIC[1], posedge WCLK &&& !IS_WCLK_INVERTED && WE, 375);
    $setup(DIC[1], negedge WCLK &&&  IS_WCLK_INVERTED && WE, 375);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L1190-L1192
    $setup(DID[0], posedge WCLK &&& !IS_WCLK_INVERTED && WE, 310);
    $setup(DID[0], negedge WCLK &&&  IS_WCLK_INVERTED && WE, 310);
    $setup(DID[1], posedge WCLK &&& !IS_WCLK_INVERTED && WE, 334);
    $setup(DID[1], negedge WCLK &&&  IS_WCLK_INVERTED && WE, 334);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L834
    $setup(WE, posedge WCLK &&& !IS_WCLK_INVERTED, 654);
    $setup(WE, negedge WCLK &&&  IS_WCLK_INVERTED, 654);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L889
    if (!IS_WCLK_INVERTED && WE) (posedge WCLK => (DOA[0] : DIA[0])) = 1153;
    if ( IS_WCLK_INVERTED && WE) (negedge WCLK => (DOA[0] : DIA[0])) = 1153;
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L857
    if (!IS_WCLK_INVERTED && WE) (posedge WCLK => (DOA[1] : DIA[1])) = 1188;
    if ( IS_WCLK_INVERTED && WE) (negedge WCLK => (DOA[1] : DIA[1])) = 1188;
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L957
    if (!IS_WCLK_INVERTED && WE) (posedge WCLK => (DOB[0] : DIB[0])) = 1161;
    if ( IS_WCLK_INVERTED && WE) (negedge WCLK => (DOB[0] : DIB[0])) = 1161;
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L925
    if (!IS_WCLK_INVERTED && WE) (posedge WCLK => (DOB[1] : DIB[1])) = 1187;
    if ( IS_WCLK_INVERTED && WE) (negedge WCLK => (DOB[1] : DIB[1])) = 1187;
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L993
    if (!IS_WCLK_INVERTED && WE) (posedge WCLK => (DOC[0] : DIC[0])) = 1158;
    if ( IS_WCLK_INVERTED && WE) (negedge WCLK => (DOC[0] : DIC[0])) = 1158;
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L1025
    if (!IS_WCLK_INVERTED && WE) (posedge WCLK => (DOC[1] : DIC[1])) = 1180;
    if ( IS_WCLK_INVERTED && WE) (negedge WCLK => (DOC[1] : DIC[1])) = 1180;
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L1093
    if (!IS_WCLK_INVERTED && WE) (posedge WCLK => (DOD[0] : DID[0])) = 1163;
    if ( IS_WCLK_INVERTED && WE) (negedge WCLK => (DOD[0] : DID[0])) = 1163;
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L1061
    if (!IS_WCLK_INVERTED && WE) (posedge WCLK => (DOD[1] : DID[1])) = 1190;
    if ( IS_WCLK_INVERTED && WE) (negedge WCLK => (DOD[1] : DID[1])) = 1190;
    // Captured by $__ABC9_RAM6
    //({{2{ADDRA[0]}},{2{ADDRB[0]}},{2{ADDRC[0]}},{2{ADDRD[0]}}} => {DOA,DOB,DOC,DOD}) = 642;
    //({{2{ADDRA[1]}},{2{ADDRB[1]}},{2{ADDRC[1]}},{2{ADDRD[1]}}} => {DOA,DOB,DOC,DOD}) = 631;
    //({{2{ADDRA[2]}},{2{ADDRB[2]}},{2{ADDRC[2]}},{2{ADDRD[2]}}} => {DOA,DOB,DOC,DOD}) = 472;
    //({{2{ADDRA[3]}},{2{ADDRB[3]}},{2{ADDRC[3]}},{2{ADDRD[3]}}} => {DOA,DOB,DOC,DOD}) = 407;
    //({{2{ADDRA[4]}},{2{ADDRB[4]}},{2{ADDRC[4]}},{2{ADDRD[4]}}} => {DOA,DOB,DOC,DOD}) = 238;
  endspecify
endmodule

module RAM32M16 (
  output [1:0] DOA,
  output [1:0] DOB,
  output [1:0] DOC,
  output [1:0] DOD,
  output [1:0] DOE,
  output [1:0] DOF,
  output [1:0] DOG,
  output [1:0] DOH,
  input [4:0] ADDRA,
  input [4:0] ADDRB,
  input [4:0] ADDRC,
  input [4:0] ADDRD,
  input [4:0] ADDRE,
  input [4:0] ADDRF,
  input [4:0] ADDRG,
  input [4:0] ADDRH,
  input [1:0] DIA,
  input [1:0] DIB,
  input [1:0] DIC,
  input [1:0] DID,
  input [1:0] DIE,
  input [1:0] DIF,
  input [1:0] DIG,
  input [1:0] DIH,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input WCLK,
  input WE
);
  parameter [63:0] INIT_A = 64'h0000000000000000;
  parameter [63:0] INIT_B = 64'h0000000000000000;
  parameter [63:0] INIT_C = 64'h0000000000000000;
  parameter [63:0] INIT_D = 64'h0000000000000000;
  parameter [63:0] INIT_E = 64'h0000000000000000;
  parameter [63:0] INIT_F = 64'h0000000000000000;
  parameter [63:0] INIT_G = 64'h0000000000000000;
  parameter [63:0] INIT_H = 64'h0000000000000000;
  parameter [0:0] IS_WCLK_INVERTED = 1'b0;
  reg [63:0] mem_a = INIT_A;
  reg [63:0] mem_b = INIT_B;
  reg [63:0] mem_c = INIT_C;
  reg [63:0] mem_d = INIT_D;
  reg [63:0] mem_e = INIT_E;
  reg [63:0] mem_f = INIT_F;
  reg [63:0] mem_g = INIT_G;
  reg [63:0] mem_h = INIT_H;
  assign DOA = mem_a[2*ADDRA+:2];
  assign DOB = mem_b[2*ADDRB+:2];
  assign DOC = mem_c[2*ADDRC+:2];
  assign DOD = mem_d[2*ADDRD+:2];
  assign DOE = mem_e[2*ADDRE+:2];
  assign DOF = mem_f[2*ADDRF+:2];
  assign DOG = mem_g[2*ADDRG+:2];
  assign DOH = mem_h[2*ADDRH+:2];
  wire clk = WCLK ^ IS_WCLK_INVERTED;
  always @(posedge clk)
    if (WE) begin
      mem_a[2*ADDRH+:2] <= DIA;
      mem_b[2*ADDRH+:2] <= DIB;
      mem_c[2*ADDRH+:2] <= DIC;
      mem_d[2*ADDRH+:2] <= DID;
      mem_e[2*ADDRH+:2] <= DIE;
      mem_f[2*ADDRH+:2] <= DIF;
      mem_g[2*ADDRH+:2] <= DIG;
      mem_h[2*ADDRH+:2] <= DIH;
    end
endmodule

module RAM64M (
  output       DOA,
  output       DOB,
  output       DOC,
  output       DOD,
  input  [5:0] ADDRA, ADDRB, ADDRC,
  input  [5:0] ADDRD,
  input        DIA,
  input        DIB,
  input        DIC,
  input        DID,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input        WCLK,
  input        WE
);
  parameter [63:0] INIT_A = 64'h0000000000000000;
  parameter [63:0] INIT_B = 64'h0000000000000000;
  parameter [63:0] INIT_C = 64'h0000000000000000;
  parameter [63:0] INIT_D = 64'h0000000000000000;
  parameter [0:0] IS_WCLK_INVERTED = 1'b0;
  reg [63:0] mem_a = INIT_A;
  reg [63:0] mem_b = INIT_B;
  reg [63:0] mem_c = INIT_C;
  reg [63:0] mem_d = INIT_D;
  assign DOA = mem_a[ADDRA];
  assign DOB = mem_b[ADDRB];
  assign DOC = mem_c[ADDRC];
  assign DOD = mem_d[ADDRD];
  wire clk = WCLK ^ IS_WCLK_INVERTED;
  always @(posedge clk)
    if (WE) begin
      mem_a[ADDRD] <= DIA;
      mem_b[ADDRD] <= DIB;
      mem_c[ADDRD] <= DIC;
      mem_d[ADDRD] <= DID;
    end
  specify
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L818-L830
    $setup(ADDRD[0], posedge WCLK &&& !IS_WCLK_INVERTED && WE, 362);
    $setup(ADDRD[0], negedge WCLK &&&  IS_WCLK_INVERTED && WE, 362);
    $setup(ADDRD[1], posedge WCLK &&& !IS_WCLK_INVERTED && WE, 245);
    $setup(ADDRD[1], negedge WCLK &&&  IS_WCLK_INVERTED && WE, 245);
    $setup(ADDRD[2], posedge WCLK &&& !IS_WCLK_INVERTED && WE, 208);
    $setup(ADDRD[2], negedge WCLK &&&  IS_WCLK_INVERTED && WE, 208);
    $setup(ADDRD[3], posedge WCLK &&& !IS_WCLK_INVERTED && WE, 147);
    $setup(ADDRD[3], negedge WCLK &&&  IS_WCLK_INVERTED && WE, 147);
    $setup(ADDRD[4], posedge WCLK &&& !IS_WCLK_INVERTED && WE, 68);
    $setup(ADDRD[4], negedge WCLK &&&  IS_WCLK_INVERTED && WE, 68);
    $setup(ADDRD[5], posedge WCLK &&& !IS_WCLK_INVERTED && WE, 66);
    $setup(ADDRD[5], negedge WCLK &&&  IS_WCLK_INVERTED && WE, 66);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L986-L988
    $setup(DIA, posedge WCLK &&& !IS_WCLK_INVERTED && WE, 384);
    $setup(DIA, negedge WCLK &&&  IS_WCLK_INVERTED && WE, 384);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L1054-L1056
    $setup(DIB, posedge WCLK &&& !IS_WCLK_INVERTED && WE, 354);
    $setup(DIB, negedge WCLK &&&  IS_WCLK_INVERTED && WE, 354);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L1122-L1124
    $setup(DIC, posedge WCLK &&& !IS_WCLK_INVERTED && WE, 375);
    $setup(DIC, negedge WCLK &&&  IS_WCLK_INVERTED && WE, 375);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L1190-L1192
    $setup(DID, posedge WCLK &&& !IS_WCLK_INVERTED && WE, 310);
    $setup(DID, negedge WCLK &&&  IS_WCLK_INVERTED && WE, 310);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L834
    $setup(WE, posedge WCLK &&& !IS_WCLK_INVERTED && WE, 654);
    $setup(WE, negedge WCLK &&&  IS_WCLK_INVERTED && WE, 654);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L889
    if (!IS_WCLK_INVERTED && WE) (posedge WCLK => (DOA : DIA)) = 1153;
    if ( IS_WCLK_INVERTED && WE) (negedge WCLK => (DOA : DIA)) = 1153;
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L957
    if (!IS_WCLK_INVERTED && WE) (posedge WCLK => (DOB : DIB)) = 1161;
    if ( IS_WCLK_INVERTED && WE) (negedge WCLK => (DOB : DIB)) = 1161;
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L1025
    if (!IS_WCLK_INVERTED && WE) (posedge WCLK => (DOC : DIC)) = 1158;
    if ( IS_WCLK_INVERTED && WE) (negedge WCLK => (DOC : DIC)) = 1158;
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L1093
    if (!IS_WCLK_INVERTED && WE) (posedge WCLK => (DOD : DID)) = 1163;
    if ( IS_WCLK_INVERTED && WE) (negedge WCLK => (DOD : DID)) = 1163;
    // Captured by $__ABC9_RAM6
    //({ADDRA[0],ADDRB[0],ADDRC[0],ADDRD[0]} => {DOA,DOB,DOC,DOD}) = 642;
    //({ADDRA[1],ADDRB[1],ADDRC[1],ADDRD[1]} => {DOA,DOB,DOC,DOD}) = 631;
    //({ADDRA[2],ADDRB[2],ADDRC[2],ADDRD[2]} => {DOA,DOB,DOC,DOD}) = 472;
    //({ADDRA[3],ADDRB[3],ADDRC[3],ADDRD[3]} => {DOA,DOB,DOC,DOD}) = 407;
    //({ADDRA[4],ADDRB[4],ADDRC[4],ADDRD[4]} => {DOA,DOB,DOC,DOD}) = 238;
  endspecify
endmodule

module RAM64M8 (
  output DOA,
  output DOB,
  output DOC,
  output DOD,
  output DOE,
  output DOF,
  output DOG,
  output DOH,
  input [5:0] ADDRA,
  input [5:0] ADDRB,
  input [5:0] ADDRC,
  input [5:0] ADDRD,
  input [5:0] ADDRE,
  input [5:0] ADDRF,
  input [5:0] ADDRG,
  input [5:0] ADDRH,
  input DIA,
  input DIB,
  input DIC,
  input DID,
  input DIE,
  input DIF,
  input DIG,
  input DIH,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input WCLK,
  input WE
);
  parameter [63:0] INIT_A = 64'h0000000000000000;
  parameter [63:0] INIT_B = 64'h0000000000000000;
  parameter [63:0] INIT_C = 64'h0000000000000000;
  parameter [63:0] INIT_D = 64'h0000000000000000;
  parameter [63:0] INIT_E = 64'h0000000000000000;
  parameter [63:0] INIT_F = 64'h0000000000000000;
  parameter [63:0] INIT_G = 64'h0000000000000000;
  parameter [63:0] INIT_H = 64'h0000000000000000;
  parameter [0:0] IS_WCLK_INVERTED = 1'b0;
  reg [63:0] mem_a = INIT_A;
  reg [63:0] mem_b = INIT_B;
  reg [63:0] mem_c = INIT_C;
  reg [63:0] mem_d = INIT_D;
  reg [63:0] mem_e = INIT_E;
  reg [63:0] mem_f = INIT_F;
  reg [63:0] mem_g = INIT_G;
  reg [63:0] mem_h = INIT_H;
  assign DOA = mem_a[ADDRA];
  assign DOB = mem_b[ADDRB];
  assign DOC = mem_c[ADDRC];
  assign DOD = mem_d[ADDRD];
  assign DOE = mem_e[ADDRE];
  assign DOF = mem_f[ADDRF];
  assign DOG = mem_g[ADDRG];
  assign DOH = mem_h[ADDRH];
  wire clk = WCLK ^ IS_WCLK_INVERTED;
  always @(posedge clk)
    if (WE) begin
      mem_a[ADDRH] <= DIA;
      mem_b[ADDRH] <= DIB;
      mem_c[ADDRH] <= DIC;
      mem_d[ADDRH] <= DID;
      mem_e[ADDRH] <= DIE;
      mem_f[ADDRH] <= DIF;
      mem_g[ADDRH] <= DIG;
      mem_h[ADDRH] <= DIH;
    end
endmodule

// ROM.

module ROM16X1 (
  output O,
  input A0, A1, A2, A3
);
  parameter [15:0] INIT = 16'h0;
  assign O = INIT[{A3, A2, A1, A0}];
endmodule

module ROM32X1 (
  output O,
  input A0, A1, A2, A3, A4
);
  parameter [31:0] INIT = 32'h0;
  assign O = INIT[{A4, A3, A2, A1, A0}];
endmodule

module ROM64X1 (
  output O,
  input A0, A1, A2, A3, A4, A5
);
  parameter [63:0] INIT = 64'h0;
  assign O = INIT[{A5, A4, A3, A2, A1, A0}];
endmodule

module ROM128X1 (
  output O,
  input A0, A1, A2, A3, A4, A5, A6
);
  parameter [127:0] INIT = 128'h0;
  assign O = INIT[{A6, A5, A4, A3, A2, A1, A0}];
endmodule

module ROM256X1 (
  output O,
  input A0, A1, A2, A3, A4, A5, A6, A7
);
  parameter [255:0] INIT = 256'h0;
  assign O = INIT[{A7, A6, A5, A4, A3, A2, A1, A0}];
endmodule

// Shift registers.

module SRL16 (
  output Q,
  input A0, A1, A2, A3,
  (* clkbuf_sink *)
  input CLK,
  input D
);
  parameter [15:0] INIT = 16'h0000;

  reg [15:0] r = INIT;
  assign Q = r[{A3,A2,A1,A0}];
  always @(posedge CLK) r <= { r[14:0], D };

  specify
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L905
    (posedge CLK => (Q : 1'bx)) = 1472;
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L912
    $setup(D , posedge CLK, 173);
    // Captured by $__ABC9_RAM6
    //(A0 => Q) = 631;
    //(A1 => Q) = 472;
    //(A2 => Q) = 407;
    //(A3 => Q) = 238;
  endspecify
endmodule

module SRL16E (
  output Q,
  input A0, A1, A2, A3, CE,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_CLK_INVERTED" *)
  input CLK,
  input D
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
  specify
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L912
    $setup(D , posedge CLK &&& !IS_CLK_INVERTED, 173);
    $setup(D , negedge CLK &&&  IS_CLK_INVERTED, 173);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L905
    if (!IS_CLK_INVERTED && CE) (posedge CLK => (Q : 1'bx)) = 1472;
    if ( IS_CLK_INVERTED && CE) (negedge CLK => (Q : 1'bx)) = 1472;
    // Captured by $__ABC9_RAM6
    //(A0 => Q) = 631;
    //(A1 => Q) = 472;
    //(A2 => Q) = 407;
    //(A3 => Q) = 238;
  endspecify
endmodule

module SRLC16 (
  output Q,
  output Q15,
  input A0, A1, A2, A3,
  (* clkbuf_sink *)
  input CLK,
  input D
);
  parameter [15:0] INIT = 16'h0000;

  reg [15:0] r = INIT;
  assign Q15 = r[15];
  assign Q = r[{A3,A2,A1,A0}];
  always @(posedge CLK) r <= { r[14:0], D };

  specify
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L905
    (posedge CLK => (Q : 1'bx)) = 1472;
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L912
    $setup(D , posedge CLK, 173);
    // Captured by $__ABC9_RAM6
    //(A0 => Q) = 631;
    //(A1 => Q) = 472;
    //(A2 => Q) = 407;
    //(A3 => Q) = 238;
  endspecify
endmodule

module SRLC16E (
  output Q,
  output Q15,
  input A0, A1, A2, A3, CE,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_CLK_INVERTED" *)
  input CLK,
  input D
);
  parameter [15:0] INIT = 16'h0000;
  parameter [0:0] IS_CLK_INVERTED = 1'b0;

  reg [15:0] r = INIT;
  assign Q15 = r[15];
  assign Q = r[{A3,A2,A1,A0}];
  generate
    if (IS_CLK_INVERTED) begin
      always @(negedge CLK) if (CE) r <= { r[14:0], D };
    end
    else
      always @(posedge CLK) if (CE) r <= { r[14:0], D };
  endgenerate
  specify
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L912
    $setup(D , posedge CLK &&& !IS_CLK_INVERTED, 173);
    $setup(D , negedge CLK &&&  IS_CLK_INVERTED, 173);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L905
    if (!IS_CLK_INVERTED && CE) (posedge CLK => (Q : D)) = 1472;
    if ( IS_CLK_INVERTED && CE) (negedge CLK => (Q : D)) = 1472;
    // Captured by $__ABC9_RAM6
    //(A0 => Q) = 642;
    //(A1 => Q) = 631;
    //(A2 => Q) = 472;
    //(A3 => Q) = 407;
    //(A4 => Q) = 238;
  endspecify
endmodule

module SRLC32E (
  output Q,
  output Q31,
  input [4:0] A,
  input CE,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_CLK_INVERTED" *)
  input CLK,
  input D
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
  specify
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L912
    $setup(D , posedge CLK &&& !IS_CLK_INVERTED, 173);
    $setup(D , negedge CLK &&&  IS_CLK_INVERTED, 173);
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L905
    if (!IS_CLK_INVERTED && CE) (posedge CLK => (Q : 1'bx)) = 1472;
    if ( IS_CLK_INVERTED && CE) (negedge CLK => (Q : 1'bx)) = 1472;
    // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L904
    if (!IS_CLK_INVERTED && CE) (posedge CLK => (Q : 1'bx)) = 1114;
    if ( IS_CLK_INVERTED && CE) (negedge CLK => (Q : 1'bx)) = 1114;
    // Captured by $__ABC9_RAM6
    //(A0 => Q) = 642;
    //(A1 => Q) = 631;
    //(A2 => Q) = 472;
    //(A3 => Q) = 407;
    //(A4 => Q) = 238;
  endspecify
endmodule

module CFGLUT5 (
  output CDO,
  output O5,
  output O6,
  input I4,
  input I3,
  input I2,
  input I1,
  input I0,
  input CDI,
  input CE,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_CLK_INVERTED" *)
  input CLK
);
  parameter [31:0] INIT = 32'h00000000;
  parameter [0:0] IS_CLK_INVERTED = 1'b0;
  wire clk = CLK ^ IS_CLK_INVERTED;
  reg [31:0] r = INIT;
  assign CDO = r[31];
  assign O5 = r[{1'b0, I3, I2, I1, I0}];
  assign O6 = r[{I4, I3, I2, I1, I0}];
  always @(posedge clk) if (CE) r <= {r[30:0], CDI};
endmodule

// DSP

// Virtex 2, Virtex 2 Pro, Spartan 3.

// Asynchronous mode.

module MULT18X18 (
    input signed [17:0] A,
    input signed [17:0] B,
    output signed [35:0] P
);

assign P = A * B;

endmodule

// Synchronous mode.

module MULT18X18S (
    input signed [17:0] A,
    input signed [17:0] B,
    output reg signed [35:0] P,
    (* clkbuf_sink *)
    input C,
    input CE,
    input R
);

always @(posedge C)
	if (R)
		P <= 0;
	else if (CE)
		P <= A * B;

endmodule

// Spartan 3E, Spartan 3A.

module MULT18X18SIO (
    input signed [17:0] A,
    input signed [17:0] B,
    output signed [35:0] P,
    (* clkbuf_sink *)
    input CLK,
    input CEA,
    input CEB,
    input CEP,
    input RSTA,
    input RSTB,
    input RSTP,
    input signed [17:0] BCIN,
    output signed [17:0] BCOUT
);

parameter integer AREG = 1;
parameter integer BREG = 1;
parameter B_INPUT = "DIRECT";
parameter integer PREG = 1;

// The multiplier.
wire signed [35:0] P_MULT;
assign P_MULT = A_MULT * B_MULT;

// The cascade output.
assign BCOUT = B_MULT;

// The B input multiplexer.
wire signed [17:0] B_MUX;
assign B_MUX = (B_INPUT == "DIRECT") ? B : BCIN;

// The registers.
reg signed [17:0] A_REG;
reg signed [17:0] B_REG;
reg signed [35:0] P_REG;

initial begin
	A_REG = 0;
	B_REG = 0;
	P_REG = 0;
end

always @(posedge CLK) begin
	if (RSTA)
		A_REG <= 0;
	else if (CEA)
		A_REG <= A;

	if (RSTB)
		B_REG <= 0;
	else if (CEB)
		B_REG <= B_MUX;

	if (RSTP)
		P_REG <= 0;
	else if (CEP)
		P_REG <= P_MULT;
end

// The register enables.
wire signed [17:0] A_MULT;
wire signed [17:0] B_MULT;
assign A_MULT = (AREG == 1) ? A_REG : A;
assign B_MULT = (BREG == 1) ? B_REG : B_MUX;
assign P = (PREG == 1) ? P_REG : P_MULT;

endmodule

// Spartan 3A DSP.

module DSP48A (
    input signed [17:0] A,
    input signed [17:0] B,
    input signed [47:0] C,
    input signed [17:0] D,
    input signed [47:0] PCIN,
    input CARRYIN,
    input [7:0] OPMODE,
    output signed [47:0] P,
    output signed [17:0] BCOUT,
    output signed [47:0] PCOUT,
    output CARRYOUT,
    (* clkbuf_sink *)
    input CLK,
    input CEA,
    input CEB,
    input CEC,
    input CED,
    input CEM,
    input CECARRYIN,
    input CEOPMODE,
    input CEP,
    input RSTA,
    input RSTB,
    input RSTC,
    input RSTD,
    input RSTM,
    input RSTCARRYIN,
    input RSTOPMODE,
    input RSTP
);

parameter integer A0REG = 0;
parameter integer A1REG = 1;
parameter integer B0REG = 0;
parameter integer B1REG = 1;
parameter integer CREG = 1;
parameter integer DREG = 1;
parameter integer MREG = 1;
parameter integer CARRYINREG = 1;
parameter integer OPMODEREG = 1;
parameter integer PREG = 1;
parameter CARRYINSEL = "CARRYIN";
parameter RSTTYPE = "SYNC";

// This is a strict subset of Spartan 6 -- reuse its model.

/* verilator lint_off PINMISSING */
DSP48A1 #(
	.A0REG(A0REG),
	.A1REG(A1REG),
	.B0REG(B0REG),
	.B1REG(B1REG),
	.CREG(CREG),
	.DREG(DREG),
	.MREG(MREG),
	.CARRYINREG(CARRYINREG),
	.CARRYOUTREG(0),
	.OPMODEREG(OPMODEREG),
	.PREG(PREG),
	.CARRYINSEL(CARRYINSEL),
	.RSTTYPE(RSTTYPE)
) upgrade (
	.A(A),
	.B(B),
	.C(C),
	.D(D),
	.PCIN(PCIN),
	.CARRYIN(CARRYIN),
	.OPMODE(OPMODE),
	// M unconnected
	.P(P),
	.BCOUT(BCOUT),
	.PCOUT(PCOUT),
	.CARRYOUT(CARRYOUT),
	// CARRYOUTF unconnected
	.CLK(CLK),
	.CEA(CEA),
	.CEB(CEB),
	.CEC(CEC),
	.CED(CED),
	.CEM(CEM),
	.CECARRYIN(CECARRYIN),
	.CEOPMODE(CEOPMODE),
	.CEP(CEP),
	.RSTA(RSTA),
	.RSTB(RSTB),
	.RSTC(RSTC),
	.RSTD(RSTD),
	.RSTM(RSTM),
	.RSTCARRYIN(RSTCARRYIN),
	.RSTOPMODE(RSTOPMODE),
	.RSTP(RSTP)
);
/* verilator lint_on PINMISSING */

endmodule

// Spartan 6.

module DSP48A1 (
    input signed [17:0] A,
    input signed [17:0] B,
    input signed [47:0] C,
    input signed [17:0] D,
    input signed [47:0] PCIN,
    input CARRYIN,
    input [7:0] OPMODE,
    output signed [35:0] M,
    output signed [47:0] P,
    output signed [17:0] BCOUT,
    output signed [47:0] PCOUT,
    output CARRYOUT,
    output CARRYOUTF,
    (* clkbuf_sink *)
    input CLK,
    input CEA,
    input CEB,
    input CEC,
    input CED,
    input CEM,
    input CECARRYIN,
    input CEOPMODE,
    input CEP,
    input RSTA,
    input RSTB,
    input RSTC,
    input RSTD,
    input RSTM,
    input RSTCARRYIN,
    input RSTOPMODE,
    input RSTP
);

parameter integer A0REG = 0;
parameter integer A1REG = 1;
parameter integer B0REG = 0;
parameter integer B1REG = 1;
parameter integer CREG = 1;
parameter integer DREG = 1;
parameter integer MREG = 1;
parameter integer CARRYINREG = 1;
parameter integer CARRYOUTREG = 1;
parameter integer OPMODEREG = 1;
parameter integer PREG = 1;
parameter CARRYINSEL = "OPMODE5";
parameter RSTTYPE = "SYNC";

wire signed [35:0] M_MULT;
wire signed [47:0] P_IN;
wire signed [17:0] A0_OUT;
wire signed [17:0] B0_OUT;
wire signed [17:0] A1_OUT;
wire signed [17:0] B1_OUT;
wire signed [17:0] B1_IN;
wire signed [47:0] C_OUT;
wire signed [17:0] D_OUT;
wire signed [7:0] OPMODE_OUT;
wire CARRYIN_OUT;
wire CARRYOUT_IN;
wire CARRYIN_IN;
reg signed [47:0] XMUX;
reg signed [47:0] ZMUX;

// The registers.
reg signed [17:0] A0_REG;
reg signed [17:0] A1_REG;
reg signed [17:0] B0_REG;
reg signed [17:0] B1_REG;
reg signed [47:0] C_REG;
reg signed [17:0] D_REG;
reg signed [35:0] M_REG;
reg signed [47:0] P_REG;
reg [7:0] OPMODE_REG;
reg CARRYIN_REG;
reg CARRYOUT_REG;

initial begin
	A0_REG = 0;
	A1_REG = 0;
	B0_REG = 0;
	B1_REG = 0;
	C_REG = 0;
	D_REG = 0;
	M_REG = 0;
	P_REG = 0;
	OPMODE_REG = 0;
	CARRYIN_REG = 0;
	CARRYOUT_REG = 0;
end

generate

if (RSTTYPE == "SYNC") begin
	always @(posedge CLK) begin
		if (RSTA) begin
			A0_REG <= 0;
			A1_REG <= 0;
		end else if (CEA) begin
			A0_REG <= A;
			A1_REG <= A0_OUT;
		end
	end

	always @(posedge CLK) begin
		if (RSTB) begin
			B0_REG <= 0;
			B1_REG <= 0;
		end else if (CEB) begin
			B0_REG <= B;
			B1_REG <= B1_IN;
		end
	end

	always @(posedge CLK) begin
		if (RSTC) begin
			C_REG <= 0;
		end else if (CEC) begin
			C_REG <= C;
		end
	end

	always @(posedge CLK) begin
		if (RSTD) begin
			D_REG <= 0;
		end else if (CED) begin
			D_REG <= D;
		end
	end

	always @(posedge CLK) begin
		if (RSTM) begin
			M_REG <= 0;
		end else if (CEM) begin
			M_REG <= M_MULT;
		end
	end

	always @(posedge CLK) begin
		if (RSTP) begin
			P_REG <= 0;
		end else if (CEP) begin
			P_REG <= P_IN;
		end
	end

	always @(posedge CLK) begin
		if (RSTOPMODE) begin
			OPMODE_REG <= 0;
		end else if (CEOPMODE) begin
			OPMODE_REG <= OPMODE;
		end
	end

	always @(posedge CLK) begin
		if (RSTCARRYIN) begin
			CARRYIN_REG <= 0;
			CARRYOUT_REG <= 0;
		end else if (CECARRYIN) begin
			CARRYIN_REG <= CARRYIN_IN;
			CARRYOUT_REG <= CARRYOUT_IN;
		end
	end
end else begin
	always @(posedge CLK, posedge RSTA) begin
		if (RSTA) begin
			A0_REG <= 0;
			A1_REG <= 0;
		end else if (CEA) begin
			A0_REG <= A;
			A1_REG <= A0_OUT;
		end
	end

	always @(posedge CLK, posedge RSTB) begin
		if (RSTB) begin
			B0_REG <= 0;
			B1_REG <= 0;
		end else if (CEB) begin
			B0_REG <= B;
			B1_REG <= B1_IN;
		end
	end

	always @(posedge CLK, posedge RSTC) begin
		if (RSTC) begin
			C_REG <= 0;
		end else if (CEC) begin
			C_REG <= C;
		end
	end

	always @(posedge CLK, posedge RSTD) begin
		if (RSTD) begin
			D_REG <= 0;
		end else if (CED) begin
			D_REG <= D;
		end
	end

	always @(posedge CLK, posedge RSTM) begin
		if (RSTM) begin
			M_REG <= 0;
		end else if (CEM) begin
			M_REG <= M_MULT;
		end
	end

	always @(posedge CLK, posedge RSTP) begin
		if (RSTP) begin
			P_REG <= 0;
		end else if (CEP) begin
			P_REG <= P_IN;
		end
	end

	always @(posedge CLK, posedge RSTOPMODE) begin
		if (RSTOPMODE) begin
			OPMODE_REG <= 0;
		end else if (CEOPMODE) begin
			OPMODE_REG <= OPMODE;
		end
	end

	always @(posedge CLK, posedge RSTCARRYIN) begin
		if (RSTCARRYIN) begin
			CARRYIN_REG <= 0;
			CARRYOUT_REG <= 0;
		end else if (CECARRYIN) begin
			CARRYIN_REG <= CARRYIN_IN;
			CARRYOUT_REG <= CARRYOUT_IN;
		end
	end
end

endgenerate

// The register enables.
assign A0_OUT = (A0REG == 1) ? A0_REG : A;
assign A1_OUT = (A1REG == 1) ? A1_REG : A0_OUT;
assign B0_OUT = (B0REG == 1) ? B0_REG : B;
assign B1_OUT = (B1REG == 1) ? B1_REG : B1_IN;
assign C_OUT = (CREG == 1) ? C_REG : C;
assign D_OUT = (DREG == 1) ? D_REG : D;
assign M = (MREG == 1) ? M_REG : M_MULT;
assign P = (PREG == 1) ? P_REG : P_IN;
assign OPMODE_OUT = (OPMODEREG == 1) ? OPMODE_REG : OPMODE;
assign CARRYIN_OUT = (CARRYINREG == 1) ? CARRYIN_REG : CARRYIN_IN;
assign CARRYOUT = (CARRYOUTREG == 1) ? CARRYOUT_REG : CARRYOUT_IN;
assign CARRYOUTF = CARRYOUT;

// The pre-adder.
wire signed [17:0] PREADDER;
assign B1_IN = OPMODE_OUT[4] ? PREADDER : B0_OUT;
assign PREADDER = OPMODE_OUT[6] ? D_OUT - B0_OUT : D_OUT + B0_OUT;

// The multiplier.
assign M_MULT = A1_OUT * B1_OUT;

// The carry in selection.
assign CARRYIN_IN = (CARRYINSEL == "OPMODE5") ? OPMODE_OUT[5] : CARRYIN;

// The post-adder inputs.
always @* begin
	case (OPMODE_OUT[1:0])
		2'b00: XMUX <= 0;
		2'b01: XMUX <= M;
		2'b10: XMUX <= P;
		2'b11: XMUX <= {D_OUT[11:0], A1_OUT, B1_OUT};
		default: XMUX <= 48'hxxxxxxxxxxxx;
	endcase
end

always @* begin
	case (OPMODE_OUT[3:2])
		2'b00: ZMUX <= 0;
		2'b01: ZMUX <= PCIN;
		2'b10: ZMUX <= P;
		2'b11: ZMUX <= C_OUT;
		default: ZMUX <= 48'hxxxxxxxxxxxx;
	endcase
end

// The post-adder.
wire signed [48:0] X_EXT;
wire signed [48:0] Z_EXT;
assign X_EXT = {1'b0, XMUX};
assign Z_EXT = {1'b0, ZMUX};
assign {CARRYOUT_IN, P_IN} = OPMODE_OUT[7] ? (Z_EXT - (X_EXT + CARRYIN_OUT)) : (Z_EXT + X_EXT + CARRYIN_OUT);

// Cascade outputs.
assign BCOUT = B1_OUT;
assign PCOUT = P;

endmodule

module DSP48 (
    input signed [17:0] A,
    input signed [17:0] B,
    input signed [47:0] C,
    input signed [17:0] BCIN,
    input signed [47:0] PCIN,
    input CARRYIN,
    input [6:0] OPMODE,
    input SUBTRACT,
    input [1:0] CARRYINSEL,
    output signed [47:0] P,
    output signed [17:0] BCOUT,
    output signed [47:0] PCOUT,
    (* clkbuf_sink *)
    input CLK,
    input CEA,
    input CEB,
    input CEC,
    input CEM,
    input CECARRYIN,
    input CECINSUB,
    input CECTRL,
    input CEP,
    input RSTA,
    input RSTB,
    input RSTC,
    input RSTM,
    input RSTCARRYIN,
    input RSTCTRL,
    input RSTP
);

parameter integer AREG = 1;
parameter integer BREG = 1;
parameter integer CREG = 1;
parameter integer MREG = 1;
parameter integer PREG = 1;
parameter integer CARRYINREG = 1;
parameter integer CARRYINSELREG = 1;
parameter integer OPMODEREG = 1;
parameter integer SUBTRACTREG = 1;
parameter B_INPUT = "DIRECT";
parameter LEGACY_MODE = "MULT18X18S";

wire signed [17:0] A_OUT;
wire signed [17:0] B_OUT;
wire signed [47:0] C_OUT;
wire signed [35:0] M_MULT;
wire signed [35:0] M_OUT;
wire signed [47:0] P_IN;
wire [6:0] OPMODE_OUT;
wire [1:0] CARRYINSEL_OUT;
wire CARRYIN_OUT;
wire SUBTRACT_OUT;
reg INT_CARRYIN_XY;
reg INT_CARRYIN_Z;
reg signed [47:0] XMUX;
reg signed [47:0] YMUX;
wire signed [47:0] XYMUX;
reg signed [47:0] ZMUX;
reg CIN;

// The B input multiplexer.
wire signed [17:0] B_MUX;
assign B_MUX = (B_INPUT == "DIRECT") ? B : BCIN;

// The cascade output.
assign BCOUT = B_OUT;
assign PCOUT = P;

// The registers.
reg signed [17:0] A0_REG;
reg signed [17:0] A1_REG;
reg signed [17:0] B0_REG;
reg signed [17:0] B1_REG;
reg signed [47:0] C_REG;
reg signed [35:0] M_REG;
reg signed [47:0] P_REG;
reg [6:0] OPMODE_REG;
reg [1:0] CARRYINSEL_REG;
reg SUBTRACT_REG;
reg CARRYIN_REG;
reg INT_CARRYIN_XY_REG;

initial begin
	A0_REG = 0;
	A1_REG = 0;
	B0_REG = 0;
	B1_REG = 0;
	C_REG = 0;
	M_REG = 0;
	P_REG = 0;
	OPMODE_REG = 0;
	CARRYINSEL_REG = 0;
	SUBTRACT_REG = 0;
	CARRYIN_REG = 0;
	INT_CARRYIN_XY_REG = 0;
end

always @(posedge CLK) begin
	if (RSTA) begin
		A0_REG <= 0;
		A1_REG <= 0;
	end else if (CEA) begin
		A0_REG <= A;
		A1_REG <= A0_REG;
	end
	if (RSTB) begin
		B0_REG <= 0;
		B1_REG <= 0;
	end else if (CEB) begin
		B0_REG <= B_MUX;
		B1_REG <= B0_REG;
	end
	if (RSTC) begin
		C_REG <= 0;
	end else if (CEC) begin
		C_REG <= C;
	end
	if (RSTM) begin
		M_REG <= 0;
	end else if (CEM) begin
		M_REG <= M_MULT;
	end
	if (RSTP) begin
		P_REG <= 0;
	end else if (CEP) begin
		P_REG <= P_IN;
	end
	if (RSTCTRL) begin
		OPMODE_REG <= 0;
		CARRYINSEL_REG <= 0;
		SUBTRACT_REG <= 0;
	end else begin
		if (CECTRL) begin
			OPMODE_REG <= OPMODE;
			CARRYINSEL_REG <= CARRYINSEL;
		end
		if (CECINSUB)
			SUBTRACT_REG <= SUBTRACT;
	end
	if (RSTCARRYIN) begin
		CARRYIN_REG <= 0;
		INT_CARRYIN_XY_REG <= 0;
	end else begin
		if (CECINSUB)
			CARRYIN_REG <= CARRYIN;
		if (CECARRYIN)
			INT_CARRYIN_XY_REG <= INT_CARRYIN_XY;
	end
end

// The register enables.
assign A_OUT = (AREG == 2) ? A1_REG : (AREG == 1) ? A0_REG : A;
assign B_OUT = (BREG == 2) ? B1_REG : (BREG == 1) ? B0_REG : B_MUX;
assign C_OUT = (CREG == 1) ? C_REG : C;
assign M_OUT = (MREG == 1) ? M_REG : M_MULT;
assign P = (PREG == 1) ? P_REG : P_IN;
assign OPMODE_OUT = (OPMODEREG == 1) ? OPMODE_REG : OPMODE;
assign SUBTRACT_OUT = (SUBTRACTREG == 1) ? SUBTRACT_REG : SUBTRACT;
assign CARRYINSEL_OUT = (CARRYINSELREG == 1) ? CARRYINSEL_REG : CARRYINSEL;
assign CARRYIN_OUT = (CARRYINREG == 1) ? CARRYIN_REG : CARRYIN;

// The multiplier.
assign M_MULT = A_OUT * B_OUT;

// The post-adder inputs.
always @* begin
	case (OPMODE_OUT[1:0])
		2'b00: XMUX <= 0;
		2'b10: XMUX <= P;
		2'b11: XMUX <= {{12{A_OUT[17]}}, A_OUT, B_OUT};
		default: XMUX <= 48'hxxxxxxxxxxxx;
	endcase
	case (OPMODE_OUT[1:0])
		2'b01: INT_CARRYIN_XY <= A_OUT[17] ~^ B_OUT[17];
		2'b11: INT_CARRYIN_XY <= ~A_OUT[17];
		// TODO: not tested in hardware.
		default: INT_CARRYIN_XY <= A_OUT[17] ~^ B_OUT[17];
	endcase
end

always @* begin
	case (OPMODE_OUT[3:2])
		2'b00: YMUX <= 0;
		2'b11: YMUX <= C_OUT;
		default: YMUX <= 48'hxxxxxxxxxxxx;
	endcase
end

assign XYMUX = (OPMODE_OUT[3:0] == 4'b0101) ? M_OUT : (XMUX + YMUX);

always @* begin
	case (OPMODE_OUT[6:4])
		3'b000: ZMUX <= 0;
		3'b001: ZMUX <= PCIN;
		3'b010: ZMUX <= P;
		3'b011: ZMUX <= C_OUT;
		3'b101: ZMUX <= {{17{PCIN[47]}}, PCIN[47:17]};
		3'b110: ZMUX <= {{17{P[47]}}, P[47:17]};
		default: ZMUX <= 48'hxxxxxxxxxxxx;
	endcase
	// TODO: check how all this works on actual hw.
	if (OPMODE_OUT[1:0] == 2'b10)
		INT_CARRYIN_Z <= ~P[47];
	else
		case (OPMODE_OUT[6:4])
			3'b001: INT_CARRYIN_Z <= ~PCIN[47];
			3'b010: INT_CARRYIN_Z <= ~P[47];
			3'b101: INT_CARRYIN_Z <= ~PCIN[47];
			3'b110: INT_CARRYIN_Z <= ~P[47];
			default: INT_CARRYIN_Z <= 1'bx;
		endcase
end

always @* begin
	case (CARRYINSEL_OUT)
		2'b00: CIN <= CARRYIN_OUT;
		2'b01: CIN <= INT_CARRYIN_Z;
		2'b10: CIN <= INT_CARRYIN_XY;
		2'b11: CIN <= INT_CARRYIN_XY_REG;
		default: CIN <= 1'bx;
	endcase
end

// The post-adder.
assign P_IN = SUBTRACT_OUT ? (ZMUX - (XYMUX + CIN)) : (ZMUX + XYMUX + CIN);

endmodule

// TODO: DSP48E (Virtex 5).

// Virtex 6, Series 7.

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
    reg        [4:0]  INMODEr = 5'b0;
    reg        [6:0]  OPMODEr = 7'b0;
    reg        [3:0]  ALUMODEr = 4'b0;
    reg        [2:0]  CARRYINSELr = 3'b0;

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

        if (CREG == 1) initial Dr = 25'b0;
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
            2'b10: begin X = P;
`ifndef YOSYS
                if (PREG != 1) $fatal(1, "PREG must be 1 when OPMODEr[1:0] is 2'b10");
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
            3'b010: begin Z = P;
`ifndef YOSYS
                if (PREG != 1) $fatal(1, "PREG must be 1 when OPMODEr[6:4] i0s 3'b010");
`endif
            end
            3'b011: Z = Cr;
            3'b100: begin Z = P;
`ifndef YOSYS
                if (PREG != 1) $fatal(1, "PREG must be 1 when OPMODEr[6:4] is 3'b100");
                if (OPMODEr[3:0] != 4'b1000) $fatal(1, "OPMODEr[3:0] must be 4'b1000 when OPMODEr[6:4] i0s 3'b100");
`endif
            end
            3'b101: Z = $signed(PCIN[47:17]);
            3'b110: Z = $signed(P[47:17]);
            default: Z = 48'bx;
        endcase
    end

    // Carry in
    wire A24_xnor_B17d = A_MULT[24] ~^ B_MULT[17];
    reg CARRYINr = 1'b0, A24_xnor_B17 = 1'b0;
    generate
        if (CARRYINREG == 1) begin always @(posedge CLK) if (RSTALLCARRYIN) CARRYINr <= 1'b0; else if (CECARRYIN) CARRYINr <= CARRYIN; end
        else                 always @* CARRYINr = CARRYIN;

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
            3'b100: cin_muxed = CARRYCASCOUT;
            3'b101: cin_muxed = ~P[47];
            3'b110: cin_muxed = A24_xnor_B17;
            3'b111: cin_muxed = P[47];
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

// TODO: DSP48E2 (Ultrascale).

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

