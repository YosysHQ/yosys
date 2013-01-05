//-----------------------------------------------------
// Design Name : tff_async_reset
// File Name   : tff_async_reset.v
// Function    : T flip-flop async reset
// Coder       : Deepak Kumar Tala
//-----------------------------------------------------
module tff_async_reset (
data  , // Data Input
clk   , // Clock Input
reset , // Reset input
q       // Q output
);
//-----------Input Ports---------------
input data, clk, reset ; 
//-----------Output Ports---------------
output q;
//------------Internal Variables--------
reg q;
//-------------Code Starts Here---------
always @ ( posedge clk or negedge reset)
if (~reset) begin
  q <= 1'b0;
end else if (data) begin
  q <= !q;
end

endmodule //End Of Module tff_async_reset
