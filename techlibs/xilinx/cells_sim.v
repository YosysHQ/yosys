
module IBUF(O, I);
output O;
input  I;
assign O = I;
endmodule

module OBUF(O, I);
output O;
input  I;
assign O = I;
endmodule

module BUFGP(O, I);
output O;
input  I;
assign O = I;
endmodule

module OBUFT(O, I, T);
output O;
input  I, T;
assign O = T ? 1'bz : I;
endmodule

module GND(G);
output G;
assign G = 0;
endmodule

module INV(O, I);
input I;
output O;
assign O = !I;
endmodule

module LUT1(O, I0);
parameter [1:0] INIT = 0;
input I0;
output O;
assign O = I0 ? INIT[1] : INIT[0];
endmodule

module LUT2(O, I0, I1);
parameter [3:0] INIT = 0;
input I0, I1;
output O;
wire [ 1: 0] s1 = I1 ? INIT[ 3: 2] : INIT[ 1: 0];
assign O = I0 ? s1[1] : s1[0];
endmodule

module LUT3(O, I0, I1, I2);
parameter [7:0] INIT = 0;
input I0, I1, I2;
output O;
wire [ 3: 0] s2 = I2 ? INIT[ 7: 4] : INIT[ 3: 0];
wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
assign O = I0 ? s1[1] : s1[0];
endmodule

module LUT4(O, I0, I1, I2, I3);
parameter [15:0] INIT = 0;
input I0, I1, I2, I3;
output O;
wire [ 7: 0] s3 = I3 ? INIT[15: 8] : INIT[ 7: 0];
wire [ 3: 0] s2 = I2 ?   s3[ 7: 4] :   s3[ 3: 0];
wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
assign O = I0 ? s1[1] : s1[0];
endmodule

module LUT5(O, I0, I1, I2, I3, I4);
parameter [31:0] INIT = 0;
input I0, I1, I2, I3, I4;
output O;
wire [15: 0] s4 = I4 ? INIT[31:16] : INIT[15: 0];
wire [ 7: 0] s3 = I3 ?   s4[15: 8] :   s4[ 7: 0];
wire [ 3: 0] s2 = I2 ?   s3[ 7: 4] :   s3[ 3: 0];
wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
assign O = I0 ? s1[1] : s1[0];
endmodule

module LUT6(O, I0, I1, I2, I3, I4, I5);
parameter [63:0] INIT = 0;
input I0, I1, I2, I3, I4, I5;
output O;
wire [31: 0] s5 = I5 ? INIT[63:32] : INIT[31: 0];
wire [15: 0] s4 = I4 ?   s5[31:16] :   s5[15: 0];
wire [ 7: 0] s3 = I3 ?   s4[15: 8] :   s4[ 7: 0];
wire [ 3: 0] s2 = I2 ?   s3[ 7: 4] :   s3[ 3: 0];
wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
assign O = I0 ? s1[1] : s1[0];
endmodule

module MUXCY(O, CI, DI, S);
input CI, DI, S;
output O;
assign O = S ? CI : DI;
endmodule

module MUXF7(O, I0, I1, S);
input I0, I1, S;
output O;
assign O = S ? I1 : I0;
endmodule

module MUXF8(O, I0, I1, S);
input I0, I1, S;
output O;
assign O = S ? I1 : I0;
endmodule

module VCC(P);
output P;
assign P = 1;
endmodule

module XORCY(O, CI, LI);
input CI, LI;
output O;
assign O = CI ^ LI;
endmodule

module CARRY4(CO, O, CI, CYINIT, DI, S);
output [3:0] CO, O;
input  CI, CYINIT;
input  [3:0] DI, S;
wire ci_or_cyinit;
assign O = S ^ {CO[2:0], ci_or_cyinit};
assign CO[0] = S[0] ? ci_or_cyinit : DI[0];
assign CO[1] = S[1] ? CO[0] : DI[1];
assign CO[2] = S[2] ? CO[1] : DI[2];
assign CO[3] = S[3] ? CO[2] : DI[3];
assign ci_or_cyinit = CI | CYINIT;
endmodule

/*
module FDRE (Q, C, CR, D, R);
parameter [0:0] INIT = 1'b0,
parameter [0:0] IS_C_INVERTED = 1'b0,
parameter [0:0] IS_D_INVERTED = 1'b0,
parameter [0:0] IS_R_INVERTED = 1'b0
output Q;
input C;
input CE;
input D;
input R;
// -- FIXME --
endmodule
*/

