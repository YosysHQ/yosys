module test(input [1:0] in, input select, output reg out);

always @( in or select)
    case (select)
	    0: out = in[0];
	    1: out = in[1];
	endcase
endmodule	
