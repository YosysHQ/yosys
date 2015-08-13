//-----------------------------------------------------
// Design Name : counter
// File Name   : counter.v
// Function    : 4 bit up counter
// Coder       : Deepak
//-----------------------------------------------------
module counter (clk, reset, enable, count);
input clk, reset, enable;
output [3:0] count;
reg [3:0] count;                                   

always @ (posedge clk)
if (reset == 1'b1) begin
  count <= 0;
end else if ( enable == 1'b1) begin
  count <= count + 1;
end

endmodule  
