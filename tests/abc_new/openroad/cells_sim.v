// sim models for cm_test_cells.lib and sm_test_cells.lib, from their function/ff groups
module INV(input A, output Y); assign Y = !A; endmodule
module BUF(input A, output Y); assign Y = A; endmodule
module AND2(input A, B, output Y); assign Y = A & B; endmodule
module OR2(input A, B, output Y); assign Y = A | B; endmodule
module NAND2(input A, B, output Y); assign Y = !(A & B); endmodule
module NOR2(input A, B, output Y); assign Y = !(A | B); endmodule
module ANDNOT2(input A, B, output Y); assign Y = A & !B; endmodule
module ORNOT2(input A, B, output Y); assign Y = A | !B; endmodule
module XOR2(input A, B, output Y); assign Y = A ^ B; endmodule
module XNOR2(input A, B, output Y); assign Y = !(A ^ B); endmodule
module MUX2(input A, B, S, output Y); assign Y = S ? B : A; endmodule
module AOI21(input A, B, C, output Y); assign Y = !(A & (B | C)); endmodule
module OAI21(input A, B, C, output Y); assign Y = !(A | (B & C)); endmodule
module AO21(input A, B, C, output Y); assign Y = A & (B | C); endmodule
module OA21(input A, B, C, output Y); assign Y = A | (B & C); endmodule
module TIELO(output Y); assign Y = 1'b0; endmodule
module TIEHI(output Y); assign Y = 1'b1; endmodule

module DFF(input D, CLK, output reg Q);
	always @(posedge CLK) Q <= D;
endmodule
module DFFR(input D, CLK, RST_N, output reg Q, output QN);
	always @(posedge CLK, negedge RST_N) if (!RST_N) Q <= 1'b0; else Q <= D;
	assign QN = !Q;
endmodule
module DFFS(input D, CLK, SET_N, output reg Q, output QN);
	always @(posedge CLK, negedge SET_N) if (!SET_N) Q <= 1'b1; else Q <= D;
	assign QN = !Q;
endmodule
// storage node is IQN: SET_N low clears it, RST_N low presets it
module DFFRSN(input D, CLK, RST_N, SET_N, output reg QN);
	always @(posedge CLK, negedge SET_N, negedge RST_N)
		if (!SET_N) QN <= 1'b0; else if (!RST_N) QN <= 1'b1; else QN <= !D;
endmodule
