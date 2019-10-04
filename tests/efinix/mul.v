module top
(
 input [7:0] x,
 input [7:0] y,

 output [15:0] A,
 );

assign A =  x * y;

endmodule
