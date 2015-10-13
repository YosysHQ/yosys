module main(input clk);
	reg [3:0] counter = 0;
	always @(posedge clk) begin
		if (counter == 10)
			counter <= 0;
		else
			counter <= counter + 1;
	end
	assert property (counter != 15);
	// assert property (counter <= 10);
endmodule
