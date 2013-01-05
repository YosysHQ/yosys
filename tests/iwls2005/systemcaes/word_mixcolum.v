//////////////////////////////////////////////////////////////////////
////                                                              ////
////  Mixcolumns for a 16 bit word module implementation          ////
////                                                              ////
////  This file is part of the SystemC AES                        ////
////                                                              ////
////  Description:                                                ////
////  Mixcolum for a 16 bit word                                  ////
////                                                              ////
////  Generated automatically using SystemC to Verilog translator ////
////                                                              ////
////  To Do:                                                      ////
////   - done                                                     ////
////                                                              ////
////  Author(s):                                                  ////
////      - Javier Castillo, jcastilo@opencores.org               ////
////                                                              ////
//////////////////////////////////////////////////////////////////////
////                                                              ////
//// Copyright (C) 2000 Authors and OPENCORES.ORG                 ////
////                                                              ////
//// This source file may be used and distributed without         ////
//// restriction provided that this copyright statement is not    ////
//// removed from the file and that any derivative work contains  ////
//// the original copyright notice and the associated disclaimer. ////
////                                                              ////
//// This source file is free software; you can redistribute it   ////
//// and/or modify it under the terms of the GNU Lesser General   ////
//// Public License as published by the Free Software Foundation; ////
//// either version 2.1 of the License, or (at your option) any   ////
//// later version.                                               ////
////                                                              ////
//// This source is distributed in the hope that it will be       ////
//// useful, but WITHOUT ANY WARRANTY; without even the implied   ////
//// warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR      ////
//// PURPOSE.  See the GNU Lesser General Public License for more ////
//// details.                                                     ////
////                                                              ////
//// You should have received a copy of the GNU Lesser General    ////
//// Public License along with this source; if not, download it   ////
//// from http://www.opencores.org/lgpl.shtml                     ////
////                                                              ////
//////////////////////////////////////////////////////////////////////
//
// CVS Revision History
//
// $Log: word_mixcolum.v,v $
// Revision 1.1.1.1  2004/07/05 09:46:23  jcastillo
// First import
//

module word_mixcolum(in,outx,outy);
input [31:0] in;
output [31:0] outx;
output [31:0] outy;

reg [31:0] outx;
reg [31:0] outy;

reg [7:0] a;
reg [7:0] b;
reg [7:0] c;
reg [7:0] d;
wire [7:0] x1;

wire [7:0] x2;

wire [7:0] x3;

wire [7:0] x4;

wire [7:0] y1;

wire [7:0] y2;

wire [7:0] y3;

wire [7:0] y4;


byte_mixcolum bm1 (.a(a), .b(b), .c(c), .d(d), .outx(x1), .outy(y1));
byte_mixcolum bm2 (.a(b), .b(c), .c(d), .d(a), .outx(x2), .outy(y2));
byte_mixcolum bm3 (.a(c), .b(d), .c(a), .d(b), .outx(x3), .outy(y3));
byte_mixcolum bm4 (.a(d), .b(a), .c(b), .d(c), .outx(x4), .outy(y4));


		reg[31:0] in_var;
		reg[31:0] outx_var,outy_var;
//split:
always @(  in)

begin


		
		in_var=in;
		a = (in_var[31:24]);
		b = (in_var[23:16]);
	c = (in_var[15:8]);
		d = (in_var[7:0]);
	
end
//mix:
always @(  x1 or   x2 or   x3 or   x4 or   y1 or   y2 or   y3 or   y4)

begin

		
		
		outx_var[31:24]=x1;
		outx_var[23:16]=x2;
		outx_var[15:8]=x3;
		outx_var[7:0]=x4;
		outy_var[31:24]=y1;
		outy_var[23:16]=y2;
		outy_var[15:8]=y3;
		outy_var[7:0]=y4;
		
		outx = (outx_var);
		outy = (outy_var);
	
end

endmodule
