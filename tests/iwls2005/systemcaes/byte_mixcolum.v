//////////////////////////////////////////////////////////////////////
////                                                              ////
////  Mixcolumns for 8 bit                                        ////
////                                                              ////
////  This file is part of the SystemC AES                        ////
////                                                              ////
////  Description:                                                ////
////  Mixcolum for a byte                                         ////
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
// $Log: byte_mixcolum.v,v $
// Revision 1.1.1.1  2004/07/05 09:46:23  jcastillo
// First import
//

module byte_mixcolum(a,b,c,d,outx,outy);

input [7:0] a,b,c,d;
output [7:0] outx, outy;

reg [7:0] outx, outy;

function [7:0] xtime;
input [7:0] in;
reg [3:0] xtime_t;

begin
xtime[7:5] = in[6:4];
xtime_t[3] = in[7];
xtime_t[2] = in[7];
xtime_t[1] = 0;
xtime_t[0] = in[7];
xtime[4:1] =xtime_t^in[3:0];
xtime[0] = in[7];
end
endfunction

reg [7:0] w1,w2,w3,w4,w5,w6,w7,w8,outx_var;
always @ (a, b, c, d)
begin
w1 = a ^b;
w2 = a ^c;
w3 = c ^d;
w4 = xtime(w1);
w5 = xtime(w3);
w6 = w2 ^w4 ^w5;
w7 = xtime(w6);
w8 = xtime(w7);

outx_var = b^w3^w4;
outx=outx_var;
outy=w8^outx_var;

end

endmodule
