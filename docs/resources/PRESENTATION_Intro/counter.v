module counter (clk, rst, en, count);

	input clk, rst, en;
	output reg [1:0] count;

	always @(posedge clk)
		if (rst)
			count <= 2'd0;
		else if (en)
			count <= count + 2'd1;

endmodule
