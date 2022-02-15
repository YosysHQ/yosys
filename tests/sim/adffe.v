module adffe( input d, clk, rst, en, output reg q );
	always @( posedge clk, posedge rst )
		if (rst)
			q <= 0;
		else
			if (en)
				q <= d;
endmodule
