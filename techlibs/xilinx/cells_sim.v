
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
  assign O = I;
endmodule

module OBUF(output O, input I);
  assign O = I;
endmodule

module BUFG(output O, input I);
  assign O = I;
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

module MUXCY(output O, input CI, DI, S);
  assign O = S ? CI : DI;
endmodule

module MUXF7(output O, input I0, I1, S);
  assign O = S ? I1 : I0;
endmodule

module MUXF8(output O, input I0, I1, S);
  assign O = S ? I1 : I0;
endmodule

module XORCY(output O, input CI, LI);
  assign O = CI ^ LI;
endmodule

module CARRY4(output [3:0] CO, O, input CI, CYINIT, input [3:0] DI, S);
  assign O = S ^ {CO[2:0], CI | CYINIT};
  assign CO[0] = S[0] ? CI | CYINIT : DI[0];
  assign CO[1] = S[1] ? CO[0] : DI[1];
  assign CO[2] = S[2] ? CO[1] : DI[2];
  assign CO[3] = S[3] ? CO[2] : DI[3];
endmodule

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
  parameter [0:0] INIT = 1'b0;
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
  parameter [0:0] INIT = 1'b0;
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

