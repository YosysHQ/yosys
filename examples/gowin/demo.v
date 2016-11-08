module demo (
	input clk,
	input [3:0] sw,
	output [15:0] leds,
	output [7:0] seg7dig,
	output [3:0] seg7sel
);
	localparam PRESCALE = 20;
	reg [PRESCALE+3:0] counter = 0;
	always @(posedge clk) counter <= counter + 1;
	assign leds = 1 << counter[PRESCALE +: 4];
endmodule
