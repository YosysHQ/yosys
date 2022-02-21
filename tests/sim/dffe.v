module dffe( input clk, en, d, output reg q );
	always @( posedge clk )
		if ( en )
			q <= d;
endmodule
