//-----------------------------------------------------
// Design Name : decoder_using_assign
// File Name   : decoder_using_assign.v
// Function    : decoder using assign
// Coder       : Deepak Kumar Tala
//-----------------------------------------------------
module decoder_using_assign (
binary_in   , //  4 bit binary input
decoder_out , //  16-bit out 
enable        //  Enable for the decoder
);
input [3:0] binary_in  ;
input  enable ; 
output [15:0] decoder_out ; 
        
wire [15:0] decoder_out ; 

assign decoder_out = (enable) ? (1 << binary_in) : 16'b0 ;

endmodule
