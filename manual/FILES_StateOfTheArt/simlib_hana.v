/* 
Copyright (C) 2009-2010 Parvez Ahmad
Written by Parvez Ahmad <parvez_ahmad@yahoo.co.uk>.

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.  */


module BUF (input in, output out);

assign out = in;

endmodule

module TRIBUF(input in, enable, output out);

assign out = enable ? in : 1'bz;

endmodule

module INV(input in, output out);

assign out = ~in;

endmodule

module AND2 #(parameter SIZE = 2) (input [SIZE-1:0] in, output out);

assign out = &in;

endmodule

module AND3 #(parameter SIZE = 3) (input [SIZE-1:0] in, output out);

assign out = &in;

endmodule
    
module AND4 #(parameter SIZE = 4) (input [SIZE-1:0] in, output out);

assign out = &in;

endmodule

module OR2 #(parameter SIZE = 2) (input [SIZE-1:0] in, output out);

assign out = |in;

endmodule

module OR3 #(parameter SIZE = 3) (input [SIZE-1:0] in, output out);

assign out = |in;

endmodule
    
module OR4 #(parameter SIZE = 4) (input [SIZE-1:0] in, output out);

assign out = |in;

endmodule


module NAND2 #(parameter SIZE = 2) (input [SIZE-1:0] in, output out);

assign out = ~&in;

endmodule

module NAND3 #(parameter SIZE = 3) (input [SIZE-1:0] in, output out);

assign out = ~&in;

endmodule
    
module NAND4 #(parameter SIZE = 4) (input [SIZE-1:0] in, output out);

assign out = ~&in;

endmodule

module NOR2 #(parameter SIZE = 2) (input [SIZE-1:0] in, output out);

assign out = ~|in;

endmodule

module NOR3 #(parameter SIZE = 3) (input [SIZE-1:0] in, output out);

assign out = ~|in;

endmodule
    
module NOR4 #(parameter SIZE = 4) (input [SIZE-1:0] in, output out);

assign out = ~|in;

endmodule


module XOR2 #(parameter SIZE = 2) (input [SIZE-1:0] in, output out);

assign out = ^in;

endmodule

module XOR3 #(parameter SIZE = 3) (input [SIZE-1:0] in, output out);

assign out = ^in;

endmodule
    
module XOR4 #(parameter SIZE = 4) (input [SIZE-1:0] in, output out);

assign out = ^in;

endmodule


module XNOR2 #(parameter SIZE = 2) (input [SIZE-1:0] in, output out);

assign out = ~^in;

endmodule

module XNOR3 #(parameter SIZE = 3) (input [SIZE-1:0] in, output out);

assign out = ~^in;

endmodule
    
module XNOR4 #(parameter SIZE = 4) (input [SIZE-1:0] in, output out);

assign out = ~^in;

endmodule

module DEC1 (input in, enable, output reg [1:0] out);

always @(in or enable)
    if(!enable)
	    out = 2'b00;
	else begin
	   case (in)
	       1'b0 : out = 2'b01;
	       1'b1 : out = 2'b10;
	    endcase
	end
endmodule	

module DEC2 (input [1:0] in, input enable, output reg [3:0] out);

always @(in or enable)
    if(!enable)
	    out = 4'b0000;
	else begin
	   case (in)
	       2'b00 : out = 4'b0001;
	       2'b01 : out = 4'b0010;
	       2'b10 : out = 4'b0100;
	       2'b11 : out = 4'b1000;
	    endcase
	end
endmodule	

module DEC3 (input [2:0] in, input enable, output reg [7:0] out);

always @(in or enable)
    if(!enable)
	    out = 8'b00000000;
	else begin
	   case (in)
	       3'b000 : out = 8'b00000001;
	       3'b001 : out = 8'b00000010;
	       3'b010 : out = 8'b00000100;
	       3'b011 : out = 8'b00001000;
	       3'b100 : out = 8'b00010000;
	       3'b101 : out = 8'b00100000;
	       3'b110 : out = 8'b01000000;
	       3'b111 : out = 8'b10000000;
	    endcase
	end
endmodule	

module DEC4 (input [3:0] in, input enable, output reg [15:0] out);

always @(in or enable)
    if(!enable)
	    out = 16'b0000000000000000;
	else begin
	   case (in)
	       4'b0000 : out = 16'b0000000000000001;
	       4'b0001 : out = 16'b0000000000000010;
	       4'b0010 : out = 16'b0000000000000100;
	       4'b0011 : out = 16'b0000000000001000;
	       4'b0100 : out = 16'b0000000000010000;
	       4'b0101 : out = 16'b0000000000100000;
	       4'b0110 : out = 16'b0000000001000000;
	       4'b0111 : out = 16'b0000000010000000;
	       4'b1000 : out = 16'b0000000100000000;
	       4'b1001 : out = 16'b0000001000000000;
	       4'b1010 : out = 16'b0000010000000000;
	       4'b1011 : out = 16'b0000100000000000;
	       4'b1100 : out = 16'b0001000000000000;
	       4'b1101 : out = 16'b0010000000000000;
	       4'b1110 : out = 16'b0100000000000000;
	       4'b1111 : out = 16'b1000000000000000;
	    endcase
	end
endmodule	
module DEC5 (input [4:0] in, input enable, output reg [31:0] out);

always @(in or enable)
    if(!enable)
	    out = 32'b00000000000000000000000000000000;
	else begin
	   case (in)
	       5'b00000 : out = 32'b00000000000000000000000000000001;
	       5'b00001 : out = 32'b00000000000000000000000000000010;
	       5'b00010 : out = 32'b00000000000000000000000000000100;
	       5'b00011 : out = 32'b00000000000000000000000000001000;
	       5'b00100 : out = 32'b00000000000000000000000000010000;
	       5'b00101 : out = 32'b00000000000000000000000000100000;
	       5'b00110 : out = 32'b00000000000000000000000001000000;
	       5'b00111 : out = 32'b00000000000000000000000010000000;
	       5'b01000 : out = 32'b00000000000000000000000100000000;
	       5'b01001 : out = 32'b00000000000000000000001000000000;
	       5'b01010 : out = 32'b00000000000000000000010000000000;
	       5'b01011 : out = 32'b00000000000000000000100000000000;
	       5'b01100 : out = 32'b00000000000000000001000000000000;
	       5'b01101 : out = 32'b00000000000000000010000000000000;
	       5'b01110 : out = 32'b00000000000000000100000000000000;
	       5'b01111 : out = 32'b00000000000000001000000000000000;
	       5'b10000 : out = 32'b00000000000000010000000000000000;
	       5'b10001 : out = 32'b00000000000000100000000000000000;
	       5'b10010 : out = 32'b00000000000001000000000000000000;
	       5'b10011 : out = 32'b00000000000010000000000000000000;
	       5'b10100 : out = 32'b00000000000100000000000000000000;
	       5'b10101 : out = 32'b00000000001000000000000000000000;
	       5'b10110 : out = 32'b00000000010000000000000000000000;
	       5'b10111 : out = 32'b00000000100000000000000000000000;
	       5'b11000 : out = 32'b00000001000000000000000000000000;
	       5'b11001 : out = 32'b00000010000000000000000000000000;
	       5'b11010 : out = 32'b00000100000000000000000000000000;
	       5'b11011 : out = 32'b00001000000000000000000000000000;
	       5'b11100 : out = 32'b00010000000000000000000000000000;
	       5'b11101 : out = 32'b00100000000000000000000000000000;
	       5'b11110 : out = 32'b01000000000000000000000000000000;
	       5'b11111 : out = 32'b10000000000000000000000000000000;
	    endcase
	end
endmodule	

module DEC6 (input [5:0] in, input enable, output reg [63:0] out);

always @(in or enable)
    if(!enable)
	    out = 64'b0000000000000000000000000000000000000000000000000000000000000000;
	else begin
	   case (in)
	       6'b000000 : out = 64'b0000000000000000000000000000000000000000000000000000000000000001;
	       6'b000001 : out = 64'b0000000000000000000000000000000000000000000000000000000000000010;
	       6'b000010 : out = 64'b0000000000000000000000000000000000000000000000000000000000000100;
	       6'b000011 : out = 64'b0000000000000000000000000000000000000000000000000000000000001000;
	       6'b000100 : out = 64'b0000000000000000000000000000000000000000000000000000000000010000;
	       6'b000101 : out = 64'b0000000000000000000000000000000000000000000000000000000000100000;
	       6'b000110 : out = 64'b0000000000000000000000000000000000000000000000000000000001000000;
	       6'b000111 : out = 64'b0000000000000000000000000000000000000000000000000000000010000000;
	       6'b001000 : out = 64'b0000000000000000000000000000000000000000000000000000000100000000;
	       6'b001001 : out = 64'b0000000000000000000000000000000000000000000000000000001000000000;
	       6'b001010 : out = 64'b0000000000000000000000000000000000000000000000000000010000000000;
	       6'b001011 : out = 64'b0000000000000000000000000000000000000000000000000000100000000000;
	       6'b001100 : out = 64'b0000000000000000000000000000000000000000000000000001000000000000;
	       6'b001101 : out = 64'b0000000000000000000000000000000000000000000000000010000000000000;
	       6'b001110 : out = 64'b0000000000000000000000000000000000000000000000000100000000000000;
	       6'b001111 : out = 64'b0000000000000000000000000000000000000000000000001000000000000000;
	       6'b010000 : out = 64'b0000000000000000000000000000000000000000000000010000000000000000;
	       6'b010001 : out = 64'b0000000000000000000000000000000000000000000000100000000000000000;
	       6'b010010 : out = 64'b0000000000000000000000000000000000000000000001000000000000000000;
	       6'b010011 : out = 64'b0000000000000000000000000000000000000000000010000000000000000000;
	       6'b010100 : out = 64'b0000000000000000000000000000000000000000000100000000000000000000;
	       6'b010101 : out = 64'b0000000000000000000000000000000000000000001000000000000000000000;
	       6'b010110 : out = 64'b0000000000000000000000000000000000000000010000000000000000000000;
	       6'b010111 : out = 64'b0000000000000000000000000000000000000000100000000000000000000000;
	       6'b011000 : out = 64'b0000000000000000000000000000000000000001000000000000000000000000;
	       6'b011001 : out = 64'b0000000000000000000000000000000000000010000000000000000000000000;
	       6'b011010 : out = 64'b0000000000000000000000000000000000000100000000000000000000000000;
	       6'b011011 : out = 64'b0000000000000000000000000000000000001000000000000000000000000000;
	       6'b011100 : out = 64'b0000000000000000000000000000000000010000000000000000000000000000;
	       6'b011101 : out = 64'b0000000000000000000000000000000000100000000000000000000000000000;
	       6'b011110 : out = 64'b0000000000000000000000000000000001000000000000000000000000000000;
	       6'b011111 : out = 64'b0000000000000000000000000000000010000000000000000000000000000000;

	       6'b100000 : out = 64'b0000000000000000000000000000000100000000000000000000000000000000;
	       6'b100001 : out = 64'b0000000000000000000000000000001000000000000000000000000000000000;
	       6'b100010 : out = 64'b0000000000000000000000000000010000000000000000000000000000000000;
	       6'b100011 : out = 64'b0000000000000000000000000000100000000000000000000000000000000000;
	       6'b100100 : out = 64'b0000000000000000000000000001000000000000000000000000000000000000;
	       6'b100101 : out = 64'b0000000000000000000000000010000000000000000000000000000000000000;
	       6'b100110 : out = 64'b0000000000000000000000000100000000000000000000000000000000000000;
	       6'b100111 : out = 64'b0000000000000000000000001000000000000000000000000000000000000000;
	       6'b101000 : out = 64'b0000000000000000000000010000000000000000000000000000000000000000;
	       6'b101001 : out = 64'b0000000000000000000000100000000000000000000000000000000000000000;
	       6'b101010 : out = 64'b0000000000000000000001000000000000000000000000000000000000000000;
	       6'b101011 : out = 64'b0000000000000000000010000000000000000000000000000000000000000000;
	       6'b101100 : out = 64'b0000000000000000000100000000000000000000000000000000000000000000;
	       6'b101101 : out = 64'b0000000000000000001000000000000000000000000000000000000000000000;
	       6'b101110 : out = 64'b0000000000000000010000000000000000000000000000000000000000000000;
	       6'b101111 : out = 64'b0000000000000000100000000000000000000000000000000000000000000000;
	       6'b110000 : out = 64'b0000000000000001000000000000000000000000000000000000000000000000;
	       6'b110001 : out = 64'b0000000000000010000000000000000000000000000000000000000000000000;
	       6'b110010 : out = 64'b0000000000000100000000000000000000000000000000000000000000000000;
	       6'b110011 : out = 64'b0000000000001000000000000000000000000000000000000000000000000000;
	       6'b110100 : out = 64'b0000000000010000000000000000000000000000000000000000000000000000;
	       6'b110101 : out = 64'b0000000000100000000000000000000000000000000000000000000000000000;
	       6'b110110 : out = 64'b0000000001000000000000000000000000000000000000000000000000000000;
	       6'b110111 : out = 64'b0000000010000000000000000000000000000000000000000000000000000000;
	       6'b111000 : out = 64'b0000000100000000000000000000000000000000000000000000000000000000;
	       6'b111001 : out = 64'b0000001000000000000000000000000000000000000000000000000000000000;
	       6'b111010 : out = 64'b0000010000000000000000000000000000000000000000000000000000000000;
	       6'b111011 : out = 64'b0000100000000000000000000000000000000000000000000000000000000000;
	       6'b111100 : out = 64'b0001000000000000000000000000000000000000000000000000000000000000;
	       6'b111101 : out = 64'b0010000000000000000000000000000000000000000000000000000000000000;
	       6'b111110 : out = 64'b0100000000000000000000000000000000000000000000000000000000000000;
	       6'b111111 : out = 64'b1000000000000000000000000000000000000000000000000000000000000000;
	    endcase
	end
endmodule	


module MUX2(input [1:0] in, input select, output reg out);

always @( in or select)
    case (select)
	    0: out = in[0];
	    1: out = in[1];
	endcase
endmodule	


module MUX4(input [3:0] in, input [1:0] select, output reg out);

always @( in or select)
    case (select)
	    0: out = in[0];
	    1: out = in[1];
	    2: out = in[2];
	    3: out = in[3];
	endcase
endmodule	


module MUX8(input [7:0] in, input [2:0] select, output reg out);

always @( in or select)
    case (select)
	    0: out = in[0];
	    1: out = in[1];
	    2: out = in[2];
	    3: out = in[3];
	    4: out = in[4];
	    5: out = in[5];
	    6: out = in[6];
	    7: out = in[7];
	endcase
endmodule	

module MUX16(input [15:0] in, input [3:0] select, output reg out);

always @( in or select)
    case (select)
	    0: out = in[0];
	    1: out = in[1];
	    2: out = in[2];
	    3: out = in[3];
	    4: out = in[4];
	    5: out = in[5];
	    6: out = in[6];
	    7: out = in[7];
	    8: out = in[8];
	    9: out = in[9];
	    10: out = in[10];
	    11: out = in[11];
	    12: out = in[12];
	    13: out = in[13];
	    14: out = in[14];
	    15: out = in[15];
	endcase
endmodule	

module MUX32(input [31:0] in, input [4:0] select, output reg out);

always @( in or select)
    case (select)
	    0: out = in[0];
	    1: out = in[1];
	    2: out = in[2];
	    3: out = in[3];
	    4: out = in[4];
	    5: out = in[5];
	    6: out = in[6];
	    7: out = in[7];
	    8: out = in[8];
	    9: out = in[9];
	    10: out = in[10];
	    11: out = in[11];
	    12: out = in[12];
	    13: out = in[13];
	    14: out = in[14];
	    15: out = in[15];
	    16: out = in[16];
	    17: out = in[17];
	    18: out = in[18];
	    19: out = in[19];
	    20: out = in[20];
	    21: out = in[21];
	    22: out = in[22];
	    23: out = in[23];
	    24: out = in[24];
	    25: out = in[25];
	    26: out = in[26];
	    27: out = in[27];
	    28: out = in[28];
	    29: out = in[29];
	    30: out = in[30];
	    31: out = in[31];
	endcase
endmodule	

module MUX64(input [63:0] in, input [5:0] select, output reg out);

always @( in or select)
    case (select)
	    0: out = in[0];
	    1: out = in[1];
	    2: out = in[2];
	    3: out = in[3];
	    4: out = in[4];
	    5: out = in[5];
	    6: out = in[6];
	    7: out = in[7];
	    8: out = in[8];
	    9: out = in[9];
	    10: out = in[10];
	    11: out = in[11];
	    12: out = in[12];
	    13: out = in[13];
	    14: out = in[14];
	    15: out = in[15];
	    16: out = in[16];
	    17: out = in[17];
	    18: out = in[18];
	    19: out = in[19];
	    20: out = in[20];
	    21: out = in[21];
	    22: out = in[22];
	    23: out = in[23];
	    24: out = in[24];
	    25: out = in[25];
	    26: out = in[26];
	    27: out = in[27];
	    28: out = in[28];
	    29: out = in[29];
	    30: out = in[30];
	    31: out = in[31];
	    32: out = in[32];
	    33: out = in[33];
	    34: out = in[34];
	    35: out = in[35];
	    36: out = in[36];
	    37: out = in[37];
	    38: out = in[38];
	    39: out = in[39];
	    40: out = in[40];
	    41: out = in[41];
	    42: out = in[42];
	    43: out = in[43];
	    44: out = in[44];
	    45: out = in[45];
	    46: out = in[46];
	    47: out = in[47];
	    48: out = in[48];
	    49: out = in[49];
	    50: out = in[50];
	    51: out = in[51];
	    52: out = in[52];
	    53: out = in[53];
	    54: out = in[54];
	    55: out = in[55];
	    56: out = in[56];
	    57: out = in[57];
	    58: out = in[58];
	    59: out = in[59];
	    60: out = in[60];
	    61: out = in[61];
	    62: out = in[62];
	    63: out = in[63];
	endcase
endmodule	

module ADD1(input in1, in2, cin, output out, cout);

assign {cout, out} = in1 + in2 + cin;

endmodule

module ADD2 #(parameter SIZE = 2)(input [SIZE-1:0] in1, in2, 
    input cin, output [SIZE-1:0] out, output cout);

assign {cout, out} = in1 + in2 + cin;

endmodule

module ADD4 #(parameter SIZE = 4)(input [SIZE-1:0] in1, in2, 
    input cin, output [SIZE-1:0] out, output cout);

assign {cout, out} = in1 + in2 + cin;

endmodule

module ADD8 #(parameter SIZE = 8)(input [SIZE-1:0] in1, in2, 
    input cin, output [SIZE-1:0] out, output cout);

assign {cout, out} = in1 + in2 + cin;

endmodule

module ADD16 #(parameter SIZE = 16)(input [SIZE-1:0] in1, in2, 
    input cin, output [SIZE-1:0] out, output cout);

assign {cout, out} = in1 + in2 + cin;

endmodule

module ADD32 #(parameter SIZE = 32)(input [SIZE-1:0] in1, in2, 
    input cin, output [SIZE-1:0] out, output cout);

assign {cout, out} = in1 + in2 + cin;

endmodule
module ADD64 #(parameter SIZE = 64)(input [SIZE-1:0] in1, in2, 
    input cin, output [SIZE-1:0] out, output cout);

assign {cout, out} = in1 + in2 + cin;

endmodule

module SUB1(input in1, in2, cin, output out, cout);

assign {cout, out} = in1 - in2 - cin;

endmodule

module SUB2 #(parameter SIZE = 2)(input [SIZE-1:0] in1, in2, 
    input cin, output [SIZE-1:0] out, output cout);

assign {cout, out} = in1 - in2 - cin;

endmodule

module SUB4 #(parameter SIZE = 4)(input [SIZE-1:0] in1, in2, 
    input cin, output [SIZE-1:0] out, output cout);

assign {cout, out} = in1 - in2 - cin;

endmodule

module SUB8 #(parameter SIZE = 8)(input [SIZE-1:0] in1, in2, 
    input cin, output [SIZE-1:0] out, output cout);

assign {cout, out} = in1 - in2 - cin;

endmodule

module SUB16 #(parameter SIZE = 16)(input [SIZE-1:0] in1, in2, 
    input cin, output [SIZE-1:0] out, output cout);

assign {cout, out} = in1 - in2 - cin;

endmodule

module SUB32 #(parameter SIZE = 32)(input [SIZE-1:0] in1, in2, 
    input cin, output [SIZE-1:0] out, output cout);

assign {cout, out} = in1 - in2 - cin;

endmodule
module SUB64 #(parameter SIZE = 64)(input [SIZE-1:0] in1, in2, 
    input cin, output [SIZE-1:0] out, output cout);

assign {cout, out} = in1 - in2 - cin;

endmodule

module MUL1 #(parameter SIZE = 1)(input in1, in2, output [2*SIZE-1:0] out);

assign out = in1*in2;

endmodule

module MUL2 #(parameter SIZE = 2)(input [SIZE-1:0] in1, in2, output [2*SIZE-1:0] out);

assign out = in1*in2;

endmodule

module MUL4 #(parameter SIZE = 4)(input [SIZE-1:0] in1, in2, output [2*SIZE-1:0] out);

assign out = in1*in2;

endmodule

module MUL8 #(parameter SIZE = 8)(input [SIZE-1:0] in1, in2, output [2*SIZE-1:0] out);

assign out = in1*in2;

endmodule

module MUL16 #(parameter SIZE = 16)(input [SIZE-1:0] in1, in2, output [2*SIZE-1:0] out);

assign out = in1*in2;

endmodule

module MUL32 #(parameter SIZE = 32)(input [SIZE-1:0] in1, in2, output [2*SIZE-1:0] out);

assign out = in1*in2;

endmodule

module MUL64 #(parameter SIZE = 64)(input [SIZE-1:0] in1, in2, output [2*SIZE-1:0] out);

assign out = in1*in2;

endmodule

module DIV1 #(parameter SIZE = 1)(input in1, in2, output out, rem);

assign out = in1/in2;
assign rem = in1%in2;

endmodule

module DIV2 #(parameter SIZE = 2)(input [SIZE-1:0] in1, in2, 
    output [SIZE-1:0] out, rem);

assign out = in1/in2;
assign rem = in1%in2;

endmodule

module DIV4 #(parameter SIZE = 4)(input [SIZE-1:0] in1, in2, 
    output [SIZE-1:0] out, rem);

assign out = in1/in2;
assign rem = in1%in2;

endmodule

module DIV8 #(parameter SIZE = 8)(input [SIZE-1:0] in1, in2, 
    output [SIZE-1:0] out, rem);

assign out = in1/in2;
assign rem = in1%in2;

endmodule

module DIV16 #(parameter SIZE = 16)(input [SIZE-1:0] in1, in2, 
    output [SIZE-1:0] out, rem);

assign out = in1/in2;
assign rem = in1%in2;

endmodule

module DIV32 #(parameter SIZE = 32)(input [SIZE-1:0] in1, in2, 
    output [SIZE-1:0] out, rem);

assign out = in1/in2;
assign rem = in1%in2;

endmodule

module DIV64 #(parameter SIZE = 64)(input [SIZE-1:0] in1, in2, 
    output [SIZE-1:0] out, rem);

assign out = in1/in2;
assign rem = in1%in2;

endmodule

module FF (input d, clk, output reg q);
always @( posedge clk)
    q <= d;
endmodule


module RFF(input d, clk, reset, output reg q);
always @(posedge clk or posedge reset)
    if(reset)
	    q <= 0;
	else
	    q <= d;
endmodule		

module SFF(input d, clk, set, output reg q);
always @(posedge clk or posedge set)
    if(set)
	    q <= 1;
	else
	    q <= d;
endmodule		

module RSFF(input d, clk, set, reset, output reg q);
always @(posedge clk or posedge reset or posedge set)
    if(reset)
	    q <= 0;
	else if(set)
	    q <= 1;
	else
	    q <= d;
endmodule

module SRFF(input d, clk, set, reset, output reg q);
always @(posedge clk or posedge set or posedge reset)
    if(set)
	    q <= 1;
	else if(reset)
	    q <= 0;
	else
	    q <= d;
endmodule

module LATCH(input d, enable, output reg q);
always @( d or enable)
    if(enable)
	    q <= d;
endmodule		

module RLATCH(input d, reset, enable, output reg q);
always @( d or enable or reset)
    if(enable)
	    if(reset)
		    q <= 0;
		else	
	        q <= d;
endmodule		

module LSHIFT1 #(parameter SIZE = 1)(input in, shift, val, output reg out);

always @ (in, shift, val) begin
    if(shift)
	    out = val;
	else 
	    out = in;
end

endmodule


module LSHIFT2 #(parameter SIZE = 2)(input [SIZE-1:0] in, 
    input [SIZE-1:0] shift, input val,
    output reg [SIZE-1:0] out);

always @(in or shift or val) begin
    out = in << shift;
	if(val)
	    out = out | ({SIZE-1 {1'b1} } >> (SIZE-1-shift));
end	
endmodule

module LSHIFT4 #(parameter SIZE = 4)(input [SIZE-1:0] in, 
    input [2:0] shift, input val, output reg [SIZE-1:0] out);

always @(in or shift or val) begin
    out = in << shift;
	if(val)
	    out = out | ({SIZE-1 {1'b1} } >> (SIZE-1-shift));
end	
endmodule


module LSHIFT8 #(parameter SIZE = 8)(input [SIZE-1:0] in, 
    input [3:0] shift, input val, output reg [SIZE-1:0] out);

always @(in or shift or val) begin
    out = in << shift;
	if(val)
	    out = out | ({SIZE-1 {1'b1} } >> (SIZE-1-shift));
end	
endmodule

module LSHIFT16 #(parameter SIZE = 16)(input [SIZE-1:0] in, 
    input [4:0] shift, input val, output reg [SIZE-1:0] out);

always @(in or shift or val) begin
    out = in << shift;
	if(val)
	    out = out | ({SIZE-1 {1'b1} } >> (SIZE-1-shift));
end	
endmodule

module LSHIFT32 #(parameter SIZE = 32)(input [SIZE-1:0] in, 
    input [5:0] shift, input val, output reg [SIZE-1:0] out);

always @(in or shift or val) begin
    out = in << shift;
	if(val)
	    out = out | ({SIZE-1 {1'b1} } >> (SIZE-1-shift));
end	
endmodule

module LSHIFT64 #(parameter SIZE = 64)(input [SIZE-1:0] in, 
    input [6:0] shift, input val, output reg [SIZE-1:0] out);

always @(in or shift or val) begin
    out = in << shift;
	if(val)
	    out = out | ({SIZE-1 {1'b1} } >> (SIZE-1-shift));
end	
endmodule

module RSHIFT1 #(parameter SIZE = 1)(input in, shift, val, output reg out);

always @ (in, shift, val) begin
    if(shift)
	    out = val;
	else
	    out = in;
end

endmodule

module RSHIFT2 #(parameter SIZE = 2)(input [SIZE-1:0] in, 
    input [SIZE-1:0] shift, input val,
    output reg [SIZE-1:0] out);

always @(in or shift or val) begin
    out = in >> shift;
	if(val)
	    out = out | ({SIZE-1 {1'b1} } << (SIZE-1-shift));
end	

endmodule


module RSHIFT4 #(parameter SIZE = 4)(input [SIZE-1:0] in, 
    input [2:0] shift, input val,
    output reg [SIZE-1:0] out);

always @(in or shift or val) begin
    out = in >> shift;
	if(val)
	    out = out | ({SIZE-1 {1'b1} } << (SIZE-1-shift));
end	
endmodule

module RSHIFT8 #(parameter SIZE = 8)(input [SIZE-1:0] in, 
    input [3:0] shift, input val,
    output reg [SIZE-1:0] out);

always @(in or shift or val) begin
    out = in >> shift;
	if(val)
	    out = out | ({SIZE-1 {1'b1} } << (SIZE-1-shift));
end	

endmodule

module RSHIFT16 #(parameter SIZE = 16)(input [SIZE-1:0] in, 
    input [4:0] shift, input val,
    output reg [SIZE-1:0] out);

always @(in or shift or val) begin
    out = in >> shift;
	if(val)
	    out = out | ({SIZE-1 {1'b1} } << (SIZE-1-shift));
end	
endmodule


module RSHIFT32 #(parameter SIZE = 32)(input [SIZE-1:0] in, 
    input [5:0] shift, input val,
    output reg [SIZE-1:0] out);

always @(in or shift or val) begin
    out = in >> shift;
	if(val)
	    out = out | ({SIZE-1 {1'b1} } << (SIZE-1-shift));
end	
endmodule

module RSHIFT64 #(parameter SIZE = 64)(input [SIZE-1:0] in, 
    input [6:0] shift, input val,
    output reg [SIZE-1:0] out);

always @(in or shift or val) begin
    out = in >> shift;
	if(val)
	    out = out | ({SIZE-1 {1'b1} } << (SIZE-1-shift));
end	
endmodule

module CMP1 #(parameter SIZE = 1) (input in1, in2, 
    output reg equal, unequal, greater, lesser);

always @ (in1 or in2) begin
    if(in1 == in2) begin
	    equal = 1;
		unequal = 0;
		greater = 0;
		lesser = 0;
	end	
	else begin
	    equal = 0;
		unequal = 1;

	    if(in1 < in2) begin
		    greater = 0;
		    lesser = 1;
	    end	
	    else begin
		    greater = 1;
		    lesser = 0;
	    end	
	end	
end
endmodule


module CMP2 #(parameter SIZE = 2) (input [SIZE-1:0] in1, in2, 
    output reg equal, unequal, greater, lesser);

always @ (in1 or in2) begin
    if(in1 == in2) begin
	    equal = 1;
		unequal = 0;
		greater = 0;
		lesser = 0;
	end	
	else begin
	    equal = 0;
		unequal = 1;

	    if(in1 < in2) begin
		    greater = 0;
		    lesser = 1;
	    end	
	    else begin
		    greater = 1;
		    lesser = 0;
	    end	
	end	
end
endmodule

module CMP4 #(parameter SIZE = 4) (input [SIZE-1:0] in1, in2, 
    output reg equal, unequal, greater, lesser);

always @ (in1 or in2) begin
    if(in1 == in2) begin
	    equal = 1;
		unequal = 0;
		greater = 0;
		lesser = 0;
	end	
	else begin
	    equal = 0;
		unequal = 1;

	    if(in1 < in2) begin
		    greater = 0;
		    lesser = 1;
	    end	
	    else begin
		    greater = 1;
		    lesser = 0;
	    end	
	end	
end
endmodule

module CMP8 #(parameter SIZE = 8) (input [SIZE-1:0] in1, in2, 
    output reg equal, unequal, greater, lesser);

always @ (in1 or in2) begin
    if(in1 == in2) begin
	    equal = 1;
		unequal = 0;
		greater = 0;
		lesser = 0;
	end	
	else begin
	    equal = 0;
		unequal = 1;

	    if(in1 < in2) begin
		    greater = 0;
		    lesser = 1;
	    end	
	    else begin
		    greater = 1;
		    lesser = 0;
	    end	
	end	
end
endmodule

module CMP16 #(parameter SIZE = 16) (input [SIZE-1:0] in1, in2, 
    output reg equal, unequal, greater, lesser);

always @ (in1 or in2) begin
    if(in1 == in2) begin
	    equal = 1;
		unequal = 0;
		greater = 0;
		lesser = 0;
	end	
	else begin
	    equal = 0;
		unequal = 1;

	    if(in1 < in2) begin
		    greater = 0;
		    lesser = 1;
	    end	
	    else begin
		    greater = 1;
		    lesser = 0;
	    end	
	end	
end
endmodule

module CMP32 #(parameter SIZE = 32) (input [SIZE-1:0] in1, in2, 
    output reg equal, unequal, greater, lesser);

always @ (in1 or in2) begin
    if(in1 == in2) begin
	    equal = 1;
		unequal = 0;
		greater = 0;
		lesser = 0;
	end	
	else begin
	    equal = 0;
		unequal = 1;

	    if(in1 < in2) begin
		    greater = 0;
		    lesser = 1;
	    end	
	    else begin
		    greater = 1;
		    lesser = 0;
	    end	
	end	
end
endmodule

module CMP64 #(parameter SIZE = 64) (input [SIZE-1:0] in1, in2, 
    output reg equal, unequal, greater, lesser);

always @ (in1 or in2) begin
    if(in1 == in2) begin
	    equal = 1;
		unequal = 0;
		greater = 0;
		lesser = 0;
	end	
	else begin
	    equal = 0;
		unequal = 1;

	    if(in1 < in2) begin
		    greater = 0;
		    lesser = 1;
	    end	
	    else begin
		    greater = 1;
		    lesser = 0;
	    end	
	end	
end
endmodule

module VCC (output supply1 out);
endmodule

module GND (output supply0 out);
endmodule


module INC1 #(parameter SIZE = 1) (input in, output [SIZE:0] out);

assign out = in + 1;

endmodule

module INC2 #(parameter SIZE = 2) (input [SIZE-1:0] in, output [SIZE:0] out);

assign out = in + 1;

endmodule

module INC4 #(parameter SIZE = 4) (input [SIZE-1:0] in, output [SIZE:0] out);
assign out = in + 1;

endmodule

module INC8 #(parameter SIZE = 8) (input [SIZE-1:0] in, output [SIZE:0] out);
assign out = in + 1;

endmodule

module INC16 #(parameter SIZE = 16) (input [SIZE-1:0] in, output [SIZE:0] out);
assign out = in + 1;

endmodule

module INC32 #(parameter SIZE = 32) (input [SIZE-1:0] in, output [SIZE:0] out);
assign out = in + 1;

endmodule
module INC64 #(parameter SIZE = 64) (input [SIZE-1:0] in, output [SIZE:0] out);
assign out = in + 1;

endmodule

