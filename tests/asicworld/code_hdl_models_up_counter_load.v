//-----------------------------------------------------
// Design Name : up_counter_load
// File Name   : up_counter_load.v
// Function    : Up counter with load
// Coder       : Deepak Kumar Tala
//-----------------------------------------------------
module up_counter_load    (
out      ,  // Output of the counter
data     ,  // Parallel load for the counter
load     ,  // Parallel load enable
enable   ,  // Enable counting
clk      ,  // clock input
reset       // reset input
);
//----------Output Ports--------------
output [7:0] out;
//------------Input Ports-------------- 
input [7:0] data;
input load, enable, clk, reset;
//------------Internal Variables--------
reg [7:0] out;
//-------------Code Starts Here-------
always @(posedge clk)
if (reset) begin
  out <= 8'b0 ;
end else if (load) begin
  out <= data;
end else if (enable) begin
  out <= out + 1;
end
    
endmodule  
