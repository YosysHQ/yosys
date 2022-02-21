module adff( input d, clk, rst, output reg q );
	always @( posedge clk, posedge rst )
		if (rst)
			q <= 0;
		else
			q <= d;
endmodule
