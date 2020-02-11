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

(* abc9_lut=10 *)
module $__ABC9_LUT7(output O, input I0, I1, I2, I3, I4, I5, I6);
  parameter [127:0] INIT = 0;
  wire [63: 0] s6 = I6 ? INIT[127:64] : INIT[63: 0];
  wire [31: 0] s5 = I5 ?    s6[63:32] :   s6[31: 0];
  wire [15: 0] s4 = I4 ?    s5[31:16] :   s5[15: 0];
  wire [ 7: 0] s3 = I3 ?    s4[15: 8] :   s4[ 7: 0];
  wire [ 3: 0] s2 = I2 ?    s3[ 7: 4] :   s3[ 3: 0];
  wire [ 1: 0] s1 = I1 ?    s2[ 3: 2] :   s2[ 1: 0];
  assign O = I0 ? s1[1] : s1[0];
  specify
    (I0 => O) = 1028;
    (I1 => O) = 1017;
    (I2 => O) =  858;
    (I3 => O) =  793;
    (I4 => O) =  624;
    (I5 => O) =  513;
    (I6 => O) =  464;
  endspecify
endmodule

(* abc9_lut=20 *)
module $__ABC9_LUT8(output O, input I0, I1, I2, I3, I4, I5, I6, I7);
  parameter [255:0] INIT = 0;
  wire [127: 0] s7 = I7 ? INIT[255:128] : INIT[127: 0];
  wire [ 63: 0] s6 = I6 ?   s7[127:63]  :   s7[ 64: 0];
  wire [ 31: 0] s5 = I5 ?   s6[ 63:32]  :   s6[ 31: 0];
  wire [ 15: 0] s4 = I4 ?   s5[ 31:16]  :   s5[ 15: 0];
  wire [  7: 0] s3 = I3 ?   s4[ 15: 8]  :   s4[  7: 0];
  wire [  3: 0] s2 = I2 ?   s3[  7: 4]  :   s3[  3: 0];
  wire [  1: 0] s1 = I1 ?   s2[  3: 2]  :   s2[  1: 0];
  assign O = I0 ? s1[1] : s1[0];
  specify
    (I0 => O) = 1149;
    (I1 => O) = 1138;
    (I2 => O) =  979;
    (I3 => O) =  914;
    (I4 => O) =  745;
    (I5 => O) =  634;
    (I6 => O) =  585;
    (I7 => O) =  468;
  endspecify
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

(* abc9_box_id = 1, lib_whitebox *)
module MUXF7(output O, input I0, I1, S);
  assign O = S ? I1 : I0;
endmodule

(* abc9_box_id = 2, lib_whitebox *)
module MUXF8(output O, input I0, I1, S);
  assign O = S ? I1 : I0;
endmodule

module MUXF9(output O, input I0, I1, S);
  assign O = S ? I1 : I0;
endmodule

module XORCY(output O, input CI, LI);
  assign O = CI ^ LI;
endmodule

(* abc9_box_id = 4, lib_whitebox *)
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
  (* abc9_arrival=303 *)
  output reg Q,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_C_INVERTED" *)
  input C,
  (* abc9_required=109 *)
  input CE,
  (* invertible_pin = "IS_D_INVERTED" *)
  //(* abc9_required=-46 *) // Negative required times not currently supported
  input D,
  (* invertible_pin = "IS_R_INVERTED" *)
  (* abc9_required=404 *)
  input R
);
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

(* abc9_flop, lib_whitebox *)
module FDRE_1 (
  (* abc9_arrival=303 *)
  output reg Q,
  (* clkbuf_sink *)
  input C,
  (* abc9_required=109 *)
  input CE,
  //(* abc9_required=-46 *) // Negative required times not currently supported
  input D,
  (* abc9_required=404 *)
  input R
);
  parameter [0:0] INIT = 1'b0;
  initial Q <= INIT;
  always @(negedge C) if (R) Q <= 1'b0; else if (CE) Q <= D;
endmodule

(* abc9_flop, lib_whitebox *)
module FDSE (
  (* abc9_arrival=303 *)
  output reg Q,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_C_INVERTED" *)
  input C,
  (* abc9_required=109 *)
  input CE,
  (* invertible_pin = "IS_D_INVERTED" *)
  //(* abc9_required=-46 *) // Negative required times not currently supported
  input D,
  (* invertible_pin = "IS_S_INVERTED" *)
  (* abc9_required=404 *)
  input S
);
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

(* abc9_flop, lib_whitebox *)
module FDSE_1 (
  (* abc9_arrival=303 *)
  output reg Q,
  (* clkbuf_sink *)
  input C,
  (* abc9_required=109 *)
  input CE,
  //(* abc9_required=-46 *) // Negative required times not currently supported
  input D,
  (* abc9_required=404 *)
  input S
);
  parameter [0:0] INIT = 1'b1;
  initial Q <= INIT;
  always @(negedge C) if (S) Q <= 1'b1; else if (CE) Q <= D;
endmodule

module FDRSE (
  output reg Q,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_C_INVERTED" *)
  input C,
  (* invertible_pin = "IS_CE_INVERTED" *)
  (* abc9_required=109 *)
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
  (* abc9_arrival=303 *)
  output reg Q,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_C_INVERTED" *)
  input C,
  (* abc9_required=109 *)
  input CE,
  (* invertible_pin = "IS_CLR_INVERTED" *)
  (* abc9_required=764 *)
  input CLR,
  (* invertible_pin = "IS_D_INVERTED" *)
  //(* abc9_required=-46 *) // Negative required times not currently supported
  input D
);
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

(* abc9_flop, lib_whitebox *)
module FDCE_1 (
  (* abc9_arrival=303 *)
  output reg Q,
  (* clkbuf_sink *)
  input C,
  (* abc9_required=109 *)
  input CE,
  (* abc9_required=764 *)
  input CLR,
  //(* abc9_required=-46 *) // Negative required times not currently supported
  input D
);
  parameter [0:0] INIT = 1'b0;
  initial Q <= INIT;
  always @(negedge C, posedge CLR) if (CLR) Q <= 1'b0; else if (CE) Q <= D;
endmodule

(* abc9_flop, lib_whitebox *)
module FDPE (
  (* abc9_arrival=303 *)
  output reg Q,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_C_INVERTED" *)
  input C,
  (* abc9_required=109 *)
  input CE,
  (* invertible_pin = "IS_D_INVERTED" *)
  //(* abc9_required=-46 *) // Negative required times not currently supported
  input D,
  (* invertible_pin = "IS_PRE_INVERTED" *)
  (* abc9_required=764 *)
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
  endcase endgenerate
endmodule

(* abc9_flop, lib_whitebox *)
module FDPE_1 (
  (* abc9_arrival=303 *)
  output reg Q,
  (* clkbuf_sink *)
  input C,
  (* abc9_required=109 *)
  input CE,
  //(* abc9_required=-46 *) // Negative required times not currently supported
  input D,
  (* abc9_required=764 *)
  input PRE
);
  parameter [0:0] INIT = 1'b1;
  initial Q <= INIT;
  always @(negedge C, posedge PRE) if (PRE) Q <= 1'b1; else if (CE) Q <= D;
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
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L981
  (* abc9_arrival=1153 *)
  output DPO, SPO,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L986
  (* abc9_required=453 *)
  input  D,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input  WCLK,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L834
  (* abc9_required=654 *)
  input  WE,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L800
  (* abc9_required=245 *)
  input  A0,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/clBLM_R.sdf#L798
  (* abc9_required=208 *)
  input  A1,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L796
  (* abc9_required=147 *)
  input  A2,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L794
  (* abc9_required=68 *)
  input  A3,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L792
  (* abc9_required=66 *)
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
  always @(posedge clk) if (WE) mem[a] <= D;
endmodule

module RAM32X1D_1 (
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L981
  (* abc9_arrival=1153 *)
  output DPO, SPO,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L986
  (* abc9_required=453 *)
  input  D,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input  WCLK,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L834
  (* abc9_required=654 *)
  input  WE,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L800
  (* abc9_required=245 *)
  input  A0,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/clBLM_R.sdf#L798
  (* abc9_required=208 *)
  input  A1,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L796
  (* abc9_required=147 *)
  input  A2,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L794
  (* abc9_required=68 *)
  input  A3,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L792
  (* abc9_required=66 *)
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
endmodule

module RAM64X1D (
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L981
  (* abc9_arrival=1153 *)
  output DPO, SPO,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L986
  (* abc9_required=453 *)
  input  D,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input  WCLK,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L834
  (* abc9_required=654 *)
  input  WE,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L828
  (* abc9_required=362 *)
  input  A0,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L826
  (* abc9_required=245 *)
  input  A1,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L824
  (* abc9_required=208 *)
  input  A2,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L822
  (* abc9_required=147 *)
  input  A3,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L820
  (* abc9_required=68 *)
  input  A4,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L818
  (* abc9_required=66 *)
  input  A5,
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

module RAM64X1D_1 (
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L981
  (* abc9_arrival=1153 *)
  output DPO, SPO,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L986
  (* abc9_required=453 *)
  input  D,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input  WCLK,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L834
  (* abc9_required=654 *)
  input  WE,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L828
  (* abc9_required=362 *)
  input  A0,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L826
  (* abc9_required=245 *)
  input  A1,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L824
  (* abc9_required=208 *)
  input  A2,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L822
  (* abc9_required=147 *)
  input  A3,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L820
  (* abc9_required=68 *)
  input  A4,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L818
  (* abc9_required=66 *)
  input  A5,
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
endmodule

module RAM128X1D (
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L981
  //   plus 208ps to cross MUXF7
  (* abc9_arrival=1359 *)
  output       DPO, SPO,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L986
  (* abc9_required=453 *)
  input        D,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input        WCLK,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L834
  (* abc9_required=654 *)
  input        WE,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L818-830
  (* abc9_required="616 362 245 208 147 68 66" *)
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
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L889
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L857
  (* abc9_arrival="1153 1188" *)
  output [1:0] DOA,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L957
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L925
  (* abc9_arrival="1161 1187" *)
  output [1:0] DOB,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L1025
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L993
  (* abc9_arrival="1158 1180" *)
  output [1:0] DOC,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L1093
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L1061
  (* abc9_arrival="1163 1190" *)
  output [1:0] DOD,
  input  [4:0] ADDRA, ADDRB, ADDRC,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L792-L802
  (* abc9_required="245 208 147 68 66" *)
  input  [4:0] ADDRD,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L986-L988
  (* abc9_required="453 384" *)
  input  [1:0] DIA,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L1054-L1056
  (* abc9_required="461 354" *)
  input  [1:0] DIB,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L1122-L1124
  (* abc9_required="457 375" *)
  input  [1:0] DIC,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L1190-L1192
  (* abc9_required="310 334" *)
  input  [1:0] DID,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input        WCLK,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L834
  (* abc9_required=654 *)
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
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L889
  (* abc9_arrival=1153 *)
  output       DOA,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L957
  (* abc9_arrival=1161 *)
  output       DOB,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L1025
  (* abc9_arrival=1158 *)
  output       DOC,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L1093
  (* abc9_arrival=1163 *)
  output       DOD,
  input  [5:0] ADDRA, ADDRB, ADDRC,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L818-L830
  (* abc9_required="362 245 208 147 68 66" *)
  input  [5:0] ADDRD,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L986-L988
  (* abc9_required=384 *)
  input        DIA,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L1054-L1056
  (* abc9_required=354 *)
  input        DIB,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L1122-L1124
  (* abc9_required=375 *)
  input        DIC,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L1190-L1192
  (* abc9_required=310 *)
  input        DID,
  (* clkbuf_sink *)
  (* invertible_pin = "IS_WCLK_INVERTED" *)
  input        WCLK,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/31f51ac5ec7448dd6f79a8267f147123e4413c21/artix7/timings/CLBLM_R.sdf#L834
  (* abc9_required=654 *)
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
endmodule

module SRL16E (
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L905
  (* abc9_arrival=1472 *)
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
endmodule

module SRLC32E (
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L905
  (* abc9_arrival=1472 *)
  output Q,
  // Max delay from: https://github.com/SymbiFlow/prjxray-db/blob/34ea6eb08a63d21ec16264ad37a0a7b142ff6031/artix7/timings/CLBLM_R.sdf#L904
  (* abc9_arrival=1114 *)
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
`ifdef YOSYS
    (* abc9_arrival = \P.abc9_arrival () *)
`endif
    output reg signed [47:0] P,
    output reg PATTERNBDETECT,
    output reg PATTERNDETECT,
`ifdef YOSYS
    (* abc9_arrival = \PCOUT.abc9_arrival () *)
`endif
    output [47:0] PCOUT,
    output UNDERFLOW,
`ifdef YOSYS
    (* abc9_required = \A.abc9_required () *)
`endif
    input signed [29:0] A,
    input [29:0] ACIN,
    input [3:0] ALUMODE,
`ifdef YOSYS
    (* abc9_required = \B.abc9_required () *)
`endif
    input signed [17:0] B,
    input [17:0] BCIN,
`ifdef YOSYS
    (* abc9_required = \C.abc9_required () *)
`endif
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
`ifdef YOSYS
    (* abc9_required = \D.abc9_required () *)
`endif
    input [24:0] D,
    input [4:0] INMODE,
    input MULTSIGNIN,
    input [6:0] OPMODE,
`ifdef YOSYS
    (* abc9_required = \PCIN.abc9_required () *)
`endif
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
    function integer \A.abc9_required ;
    begin
        \A.abc9_required = 0;
        if (AREG != 0)           \A.abc9_required =  254;
        else if (USE_MULT == "MULTIPLY" && USE_DPORT == "FALSE") begin
            if (MREG != 0)       \A.abc9_required = 1416;
            else if (PREG != 0)  \A.abc9_required = (USE_PATTERN_DETECT != "NO_PATDET" ? 3030 : 2739) ;
        end
        else if (USE_MULT == "MULTIPLY" && USE_DPORT == "TRUE") begin
            // Worst-case from ADREG and MREG
            if (MREG != 0)       \A.abc9_required = 2400;
            else if (ADREG != 0) \A.abc9_required = 1283;
            else if (PREG != 0)  \A.abc9_required = 3723;
            else if (PREG != 0)  \A.abc9_required = (USE_PATTERN_DETECT != "NO_PATDET" ? 4014 : 3723) ;
        end
        else if (USE_MULT == "NONE" && USE_DPORT == "FALSE") begin
            if (PREG != 0)       \A.abc9_required = (USE_PATTERN_DETECT != "NO_PATDET" ? 1730 : 1441) ;
        end
    end
    endfunction
    function integer \B.abc9_required ;
    begin
        \B.abc9_required = 0;
        if (BREG != 0)      \B.abc9_required =  324;
        else if (MREG != 0) \B.abc9_required = 1285;
        else if (USE_MULT == "MULTIPLY" && USE_DPORT == "FALSE") begin
            if (PREG != 0)  \B.abc9_required = (USE_PATTERN_DETECT != "NO_PATDET" ? 2898 : 2608) ;
        end
        else if (USE_MULT == "MULTIPLY" && USE_DPORT == "TRUE") begin
            if (PREG != 0)  \B.abc9_required = (USE_PATTERN_DETECT != "NO_PATDET" ? 2898 : 2608) ;
        end
        else if (USE_MULT == "NONE" && USE_DPORT == "FALSE") begin
            if (PREG != 0)  \B.abc9_required = (USE_PATTERN_DETECT != "NO_PATDET" ? 1718 : 1428) ;
        end
    end
    endfunction
    function integer \C.abc9_required ;
    begin
        \C.abc9_required = 0;
        if (CREG != 0)      \C.abc9_required =  168;
        else if (PREG != 0) \C.abc9_required = (USE_PATTERN_DETECT != "NO_PATDET" ? 1534 : 1244) ;
    end
    endfunction
    function integer \D.abc9_required ;
    begin
        \D.abc9_required = 0;
        if (USE_MULT == "MULTIPLY" && USE_DPORT == "FALSE") begin
        end
        else if (USE_MULT == "MULTIPLY" && USE_DPORT == "TRUE") begin
            if (DREG != 0)       \D.abc9_required =  248;
            else if (ADREG != 0) \D.abc9_required = 1195;
            else if (MREG != 0)  \D.abc9_required = 2310;
            else if (PREG != 0)  \D.abc9_required = (USE_PATTERN_DETECT != "NO_PATDET" ? 3925 : 3635) ;
        end
        else if (USE_MULT == "NONE" && USE_DPORT == "FALSE") begin
        end
    end
    endfunction
    function integer \PCIN.abc9_required ;
    begin
        \PCIN.abc9_required = 0;
        if (PREG != 0) \PCIN.abc9_required = (USE_PATTERN_DETECT != "NO_PATDET" ? 1315 : 1025) ;
    end
    endfunction
    function integer \P.abc9_arrival ;
    begin
        \P.abc9_arrival = 0;
        if (USE_MULT == "MULTIPLY" && USE_DPORT == "FALSE") begin
            if (PREG != 0)       \P.abc9_arrival =  329;
            // Worst-case from CREG and MREG
            else if (CREG != 0)  \P.abc9_arrival = 1687;
            else if (MREG != 0)  \P.abc9_arrival = 1671;
            // Worst-case from AREG and BREG
            else if (AREG != 0)  \P.abc9_arrival = 2952;
            else if (BREG != 0)  \P.abc9_arrival = 2813;
        end
        else if (USE_MULT == "MULTIPLY" && USE_DPORT == "TRUE") begin
            if (PREG != 0)       \P.abc9_arrival =  329;
            // Worst-case from CREG and MREG
            else if (CREG != 0)  \P.abc9_arrival = 1687;
            else if (MREG != 0)  \P.abc9_arrival = 1671;
            // Worst-case from AREG, ADREG, BREG, DREG
            else if (AREG != 0)  \P.abc9_arrival = 3935;
            else if (DREG != 0)  \P.abc9_arrival = 3908;
            else if (ADREG != 0) \P.abc9_arrival = 2958;
            else if (BREG != 0)  \P.abc9_arrival = 2813;
        end
        else if (USE_MULT == "NONE" && USE_DPORT == "FALSE") begin
            if (PREG != 0)       \P.abc9_arrival =  329;
            // Worst-case from AREG, BREG, CREG
            else if (CREG != 0)  \P.abc9_arrival = 1687;
            else if (AREG != 0)  \P.abc9_arrival = 1632;
            else if (BREG != 0)  \P.abc9_arrival = 1616;
        end
        //else
        //    $error("Invalid DSP48E1 configuration");
    end
    endfunction
    function integer \PCOUT.abc9_arrival ;
    begin
        \PCOUT.abc9_arrival = 0;
        if (USE_MULT == "MULTIPLY" && USE_DPORT == "FALSE") begin
            if (PREG != 0)       \PCOUT.abc9_arrival =  435;
            // Worst-case from CREG and MREG
            else if (CREG != 0)  \PCOUT.abc9_arrival = 1835;
            else if (MREG != 0)  \PCOUT.abc9_arrival = 1819;
            // Worst-case from AREG and BREG
            else if (AREG != 0)  \PCOUT.abc9_arrival = 3098;
            else if (BREG != 0)  \PCOUT.abc9_arrival = 2960;
        end
        else if (USE_MULT == "MULTIPLY" && USE_DPORT == "TRUE") begin
            if (PREG != 0)       \PCOUT.abc9_arrival =  435;
            // Worst-case from CREG and MREG
            else if (CREG != 0)  \PCOUT.abc9_arrival = 1835;
            else if (MREG != 0)  \PCOUT.abc9_arrival = 1819;
            // Worst-case from AREG, ADREG, BREG, DREG
            else if (AREG != 0)  \PCOUT.abc9_arrival = 4083;
            else if (DREG != 0)  \PCOUT.abc9_arrival = 4056;
            else if (BREG != 0)  \PCOUT.abc9_arrival = 2960;
            else if (ADREG != 0) \PCOUT.abc9_arrival = 2859;
        end
        else if (USE_MULT == "NONE" && USE_DPORT == "FALSE") begin
            if (PREG != 0)       \PCOUT.abc9_arrival =  435;
            // Worst-case from AREG, BREG, CREG
            else if (CREG != 0)  \PCOUT.abc9_arrival = 1835;
            else if (AREG != 0)  \PCOUT.abc9_arrival = 1780;
            else if (BREG != 0)  \PCOUT.abc9_arrival = 1765;
        end
        //else
        //    $error("Invalid DSP48E1 configuration");
    end
    endfunction
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
