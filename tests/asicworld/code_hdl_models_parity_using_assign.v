//-----------------------------------------------------
// Design Name : parity_using_assign
// File Name   : parity_using_assign.v
// Function    : Parity using assign
// Coder       : Deepak Kumar Tala
//-----------------------------------------------------
module parity_using_assign (
data_in    , //  8 bit data in
parity_out   //  1 bit parity out
);
output  parity_out ;
input [7:0] data_in ; 
     
wire parity_out ;
      
assign parity_out =  (data_in[0] ^ data_in[1]) ^  
                     (data_in[2] ^ data_in[3]) ^ 
                     (data_in[4] ^ data_in[5]) ^  
                     (data_in[6] ^ data_in[7]);

endmodule 
