module dffsr( input clk, d, clr, set, output reg q );
	always @( posedge clk, posedge set, posedge clr)
		if ( clr )
			q <= 0;
		else if (set)
			q <= 1;
		else
			q <= d;
endmodule
