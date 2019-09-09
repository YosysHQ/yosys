// Multiplexer using case statement 
module mux4 (sel, a, b, c, d, outmux);
input [1:0] sel;
input [1:0] a, b, c, d;
output [1:0] outmux;
reg [1:0] outmux;

always @ *
   begin 
	   case(sel)
		  2'b00 : outmux = a;
      2'b01 : outmux = b;
      2'b10 : outmux = c;
      2'b11 : outmux = d;
     endcase
   end 
endmodule

