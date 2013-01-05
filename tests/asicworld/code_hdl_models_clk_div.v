//-----------------------------------------------------
// Design Name : clk_div
// File Name   : clk_div.v
// Function    : Divide by two counter
// Coder       : Deepak Kumar Tala
//-----------------------------------------------------

module clk_div (clk_in, enable,reset, clk_out);
 // --------------Port Declaration----------------------- 
 input               clk_in                   ;
 input               reset                    ;
 input               enable                   ;
 output              clk_out                  ;
 //--------------Port data type declaration-------------
 wire                 clk_in                  ;
 wire                 enable                  ;
//--------------Internal Registers----------------------
reg                   clk_out                 ;
//--------------Code Starts Here----------------------- 
always @ (posedge clk_in) 
if (reset) begin 
  clk_out <= 1'b0;
end else if (enable) begin
  clk_out <= !clk_out ; 
end

endmodule  
