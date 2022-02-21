module aldff( input [0:3] d, input [0:3] ad, input clk, aload, output reg [0:3] q );
	always @( posedge clk, posedge aload)
		if (aload)
			q <= ad;
		else
			q <= d;
endmodule
