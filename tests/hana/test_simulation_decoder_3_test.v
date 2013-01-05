module test (input [1:0] in, input enable, output reg [2:0] out);

always @(in or enable)
    if(!enable)
	    out = 3'b000;
	else begin
	   case (in)
	       2'b00 : out = 3'b001 ;
	       2'b01 : out = 3'b010;
	       2'b10 : out = 3'b010;
	       2'b11 : out = 3'b100;
	    endcase
	end
endmodule
