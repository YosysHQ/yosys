module testbench;
	reg clk;

	initial begin
		#5 clk = 0;
		forever #5 clk = ~clk;
	end

	wire [15:0] leds;

	initial begin
		// $dumpfile("testbench.vcd");
		// $dumpvars(0, testbench);
		$monitor("%b", leds);
	end

	demo uut (
		.clk  (clk  ),
`ifdef POST_IMPL
		.\leds[0]  (leds[0]),
		.\leds[1]  (leds[1]),
		.\leds[2]  (leds[2]),
		.\leds[3]  (leds[3]),
		.\leds[4]  (leds[4]),
		.\leds[5]  (leds[5]),
		.\leds[6]  (leds[6]),
		.\leds[7]  (leds[7]),
		.\leds[8]  (leds[8]),
		.\leds[9]  (leds[9]),
		.\leds[10] (leds[10]),
		.\leds[11] (leds[11]),
		.\leds[12] (leds[12]),
		.\leds[13] (leds[13]),
		.\leds[14] (leds[14]),
		.\leds[15] (leds[15])
`else
		.leds(leds)
`endif
	);
endmodule
