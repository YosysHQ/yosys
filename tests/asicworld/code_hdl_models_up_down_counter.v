//-----------------------------------------------------
// Design Name : up_down_counter
// File Name   : up_down_counter.v
// Function    : Up down counter
// Coder       : Deepak Kumar Tala
//-----------------------------------------------------
module up_down_counter    (
out      ,  // Output of the counter
up_down  ,  // up_down control for counter
clk      ,  // clock input
reset       // reset input
);
//----------Output Ports--------------
output [7:0] out;
//------------Input Ports-------------- 
input up_down, clk, reset;
//------------Internal Variables--------
reg [7:0] out;
//-------------Code Starts Here-------
always @(posedge clk)
if (reset) begin // active high reset
  out <= 8'b0 ;
end else if (up_down) begin
  out <= out + 1;
end else begin
  out <= out - 1;
end

endmodule 
