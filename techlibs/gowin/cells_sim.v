module LUT1(output F, input I0);
	parameter [1:0] INIT = 0;
	assign F = I0 ? INIT[1] : INIT[0];
endmodule

module LUT2(output F, input I0, I1);
	parameter [3:0] INIT = 0;
	wire [ 1: 0] s1 = I1 ? INIT[ 3: 2] : INIT[ 1: 0];
	assign F = I0 ? s1[1] : s1[0];
endmodule

module LUT3(output F, input I0, I1, I2);
	parameter [7:0] INIT = 0;
	wire [ 3: 0] s2 = I2 ? INIT[ 7: 4] : INIT[ 3: 0];
	wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
	assign F = I0 ? s1[1] : s1[0];
endmodule

module LUT4(output F, input I0, I1, I2, I3);
	parameter [15:0] INIT = 0;
	wire [ 7: 0] s3 = I3 ? INIT[15: 8] : INIT[ 7: 0];
	wire [ 3: 0] s2 = I2 ?   s3[ 7: 4] :   s3[ 3: 0];
	wire [ 1: 0] s1 = I1 ?   s2[ 3: 2] :   s2[ 1: 0];
	assign F = I0 ? s1[1] : s1[0];
endmodule

module DFF (output reg Q, input CLK, D);
	parameter [0:0] INIT = 1'b0;
	initial Q = INIT;
	always @(posedge CLK)
		Q <= D;
endmodule

module DFFN (output reg Q, input CLK, D);
	parameter [0:0] INIT = 1'b0;
	initial Q = INIT;
	always @(negedge CLK)
		Q <= D;
endmodule

module VCC(output V);
	assign V = 1;
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

module GSR (input GSRI);
	wire GSRO = GSRI;
endmodule

module ALU (input I0, input I1, input I3, input CIN, output COUT, output SUM);
   parameter [3:0] ALU_MODE = 0; // default 0 = ADD
   assign  {COUT, SUM} = CIN + I1 + I0;
endmodule // alu

