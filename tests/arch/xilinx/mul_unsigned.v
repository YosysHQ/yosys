/*
Example from: https://www.xilinx.com/support/documentation/sw_manuals/xilinx2019_1/ug901-vivado-synthesis.pdf [p. 89].
*/

// Unsigned 16x24-bit Multiplier
// 1 latency stage on operands
// 3 latency stage after the multiplication
// File: multipliers2.v
//
module mul_unsigned (clk, A, B, RES);
parameter WIDTHA = /*16*/ 6;
parameter WIDTHB = /*24*/ 9;
input clk;
input [WIDTHA-1:0] A;
input [WIDTHB-1:0] B;
output [WIDTHA+WIDTHB-1:0] RES;
reg [WIDTHA-1:0] rA;
reg [WIDTHB-1:0] rB;
reg [WIDTHA+WIDTHB-1:0] M [3:0];
integer i;
always @(posedge clk)
 begin
 rA <= A;
 rB <= B;
 M[0] <= rA * rB;
 for (i = 0; i < 3; i = i+1)
 M[i+1] <= M[i];
 end
assign RES = M[3];
endmodule
