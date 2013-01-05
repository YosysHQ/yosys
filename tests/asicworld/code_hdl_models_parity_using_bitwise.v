//-----------------------------------------------------
// Design Name : parity_using_bitwise
// File Name   : parity_using_bitwise.v
// Function    : Parity using bitwise xor
// Coder       : Deepak Kumar Tala
//-----------------------------------------------------
module parity_using_bitwise (
data_in    , //  8 bit data in
parity_out   //  1 bit parity out
);
output  parity_out ;
input [7:0] data_in ; 
     
assign parity_out = ^data_in; 

endmodule
