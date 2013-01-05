//-----------------------------------------------------
// Design Name : encoder_using_case
// File Name   : encoder_using_case.v
// Function    : Encoder using Case
// Coder       : Deepak Kumar Tala
//-----------------------------------------------------
module encoder_using_case(
binary_out , //  4 bit binary Output
encoder_in , //  16-bit Input
enable       //  Enable for the encoder
);
output [3:0] binary_out  ;
input  enable ; 
input [15:0] encoder_in ; 
     
reg [3:0] binary_out ;
      
always @ (enable or encoder_in)
begin
  binary_out = 0;
  if (enable) begin
    case (encoder_in) 
      16'h0002 : binary_out = 1; 
      16'h0004 : binary_out = 2; 
      16'h0008 : binary_out = 3; 
      16'h0010 : binary_out = 4;
      16'h0020 : binary_out = 5; 
      16'h0040 : binary_out = 6; 
      16'h0080 : binary_out = 7; 
      16'h0100 : binary_out = 8;
      16'h0200 : binary_out = 9;
      16'h0400 : binary_out = 10; 
      16'h0800 : binary_out = 11; 
      16'h1000 : binary_out = 12; 
      16'h2000 : binary_out = 13; 
      16'h4000 : binary_out = 14; 
      16'h8000 : binary_out = 15; 
   endcase
  end
end

endmodule
