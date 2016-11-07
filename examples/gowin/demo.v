module demo (
	input clk,
	output led1, led2, led3, led4, led5, led6, led7, led8,
	output led9, led10, led11, led12, led13, led14, led15, led16
);
	localparam PRESCALE = 20;
	reg [PRESCALE+3:0] counter = 0;
	always @(posedge clk) counter <= counter + 1;
	assign {led1, led2, led3, led4, led5, led6, led7, led8,
	        led9, led10, led11, led12, led13, led14, led15, led16} = 1 << counter[PRESCALE +: 4];
endmodule
