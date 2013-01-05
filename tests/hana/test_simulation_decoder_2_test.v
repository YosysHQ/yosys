module test (input [1:0] in, input enable, output reg  out);

always @(in or enable)
    if(!enable)
	    out = 4'b0000;
	else begin
	   case (in)
	       2'b00 : out = 0 ;
	       2'b01 : out = 1;
	       2'b10 : out = 0;
	       2'b11 : out = 1;
	    endcase
	end
endmodule
