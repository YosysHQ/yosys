
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
parameter INIT = 0;
input I0;
wire [1:0] lutdata = INIT;
wire [0:0] idx = { I0 };
output O;
assign O = lutdata[idx];
endmodule

module LUT2(O, I0, I1);
parameter INIT = 0;
input I0, I1;
wire [3:0] lutdata = INIT;
wire [1:0] idx = { I1, I0 };
output O;
assign O = lutdata[idx];
endmodule

module LUT3(O, I0, I1, I2);
parameter INIT = 0;
input I0, I1, I2;
wire [7:0] lutdata = INIT;
wire [2:0] idx = { I2, I1, I0 };
output O;
assign O = lutdata[idx];
endmodule

module LUT4(O, I0, I1, I2, I3);
parameter INIT = 0;
input I0, I1, I2, I3;
wire [15:0] lutdata = INIT;
wire [3:0] idx = { I3, I2, I1, I0 };
output O;
assign O = lutdata[idx];
endmodule

module LUT5(O, I0, I1, I2, I3, I4);
parameter INIT = 0;
input I0, I1, I2, I3, I4;
wire [31:0] lutdata = INIT;
wire [4:0] idx = { I4, I3, I2, I1, I0 };
output O;
assign O = lutdata[idx];
endmodule

module LUT6(O, I0, I1, I2, I3, I4, I5);
parameter INIT = 0;
input I0, I1, I2, I3, I4, I5;
wire [63:0] lutdata = INIT;
wire [5:0] idx = { I5, I4, I3, I2, I1, I0 };
output O;
assign O = lutdata[idx];
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

