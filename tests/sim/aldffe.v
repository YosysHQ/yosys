module aldffe( input [0:3] d, input [0:3] ad, input clk, aload, en, output reg [0:3] q );
	always @( posedge clk, posedge aload)
		if (aload)
			q <= ad;
		else
			if (en)
				q <= d;
endmodule
