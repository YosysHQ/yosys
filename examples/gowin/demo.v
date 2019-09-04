module demo (
	input clk,
	output [15:0] leds
);
	localparam PRESCALE = 20;
	reg [PRESCALE+3:0] counter = 0;
	always @(posedge clk) counter <= counter + 1;
	assign leds = 1 << counter[PRESCALE +: 4];
endmodule
