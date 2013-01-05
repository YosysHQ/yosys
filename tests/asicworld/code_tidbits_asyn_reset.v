module  asyn_reset(clk,reset,a,c);
     input clk;
     input reset;
     input a;
     output c; 

   wire clk;
   wire reset;   
   wire a;    
   reg c;
        
always @ (posedge clk or posedge reset)
 if ( reset == 1'b1) begin
   c <= 0;
 end else begin
   c <= a;
 end
endmodule
