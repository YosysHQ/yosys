//-----------------------------------------------------
// Design Name : one_hot_cnt
// File Name   : one_hot_cnt.v
// Function    : 8 bit one hot counter
// Coder       : Deepak Kumar Tala
//-----------------------------------------------------
module one_hot_cnt (
out        ,  // Output of the counter
enable     ,  // enable for counter
clk        ,  // clock input
reset         // reset input
);
//----------Output Ports--------------
output [7:0] out;

//------------Input Ports--------------
input enable, clk, reset;

//------------Internal Variables--------
reg [7:0] out;  

//-------------Code Starts Here-------
always @ (posedge clk)
if (reset) begin
  out <= 8'b0000_0001 ;
end else if (enable) begin
  out <= {out[6],out[5],out[4],out[3],
          out[2],out[1],out[0],out[7]};
end

endmodule  
