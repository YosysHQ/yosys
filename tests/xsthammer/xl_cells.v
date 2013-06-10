
module GND(G);
output G = 0;
endmodule

module INV(O, I);
input I;
output O = !I;
endmodule

module LUT2(O, I0, I1);
parameter INIT = 0;
input I0, I1;
wire [3:0] lutdata = INIT;
wire [1:0] idx = { I1, I0 };
output O = lutdata[idx];
endmodule

module LUT3(O, I0, I1, I2);
parameter INIT = 0;
input I0, I1, I2;
wire [7:0] lutdata = INIT;
wire [2:0] idx = { I2, I1, I0 };
output O = lutdata[idx];
endmodule

module LUT4(O, I0, I1, I2, I3);
parameter INIT = 0;
input I0, I1, I2, I3;
wire [15:0] lutdata = INIT;
wire [3:0] idx = { I3, I2, I1, I0 };
output O = lutdata[idx];
endmodule

module LUT5(O, I0, I1, I2, I3, I4);
parameter INIT = 0;
input I0, I1, I2, I3, I4;
wire [31:0] lutdata = INIT;
wire [4:0] idx = { I4, I3, I2, I1, I0 };
output O = lutdata[idx];
endmodule

module LUT6(O, I0, I1, I2, I3, I4, I5);
parameter INIT = 0;
input I0, I1, I2, I3, I4, I5;
wire [63:0] lutdata = INIT;
wire [5:0] idx = { I5, I4, I3, I2, I1, I0 };
output O = lutdata[idx];
endmodule

module MUXCY(O, CI, DI, S);
input CI, DI, S;
output O = S ? CI : DI;
endmodule

module MUXF7(O, I0, I1, S);
input I0, I1, S;
output O = S ? I1 : I0;
endmodule

module VCC(P);
output P = 1;
endmodule

module XORCY(O, CI, LI);
input CI, LI;
output O = CI ^ LI;
endmodule

