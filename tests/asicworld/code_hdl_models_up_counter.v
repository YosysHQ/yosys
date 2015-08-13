//-----------------------------------------------------
// Design Name : up_counter
// File Name   : up_counter.v
// Function    : Up counter
// Coder       : Deepak
//-----------------------------------------------------
module up_counter    (
out     ,  // Output of the counter
enable  ,  // enable for counter
clk     ,  // clock Input
reset      // reset Input
);
//----------Output Ports--------------
    output [7:0] out;
//------------Input Ports--------------
     input enable, clk, reset;
//------------Internal Variables--------
    reg [7:0] out;
//-------------Code Starts Here-------
always @(posedge clk)
if (reset) begin
  out <= 8'b0 ;
end else if (enable) begin
  out <= out + 1;
end


endmodule 

