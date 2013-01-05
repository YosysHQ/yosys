module test(input  in,  input clk,  output reg out);
always @(negedge clk)
   out <= in;
endmodule	
