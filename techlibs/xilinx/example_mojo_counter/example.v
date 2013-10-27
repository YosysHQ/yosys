module top(clk, ctrl, led_7, led_6, led_5, led_4, led_3, led_2, led_1, led_0);

input clk, ctrl;
output led_7, led_6, led_5, led_4;
output led_3, led_2, led_1, led_0;

reg [31:0] counter;

always @(posedge clk)
	counter <= counter + (ctrl ? 4 : 1);

assign {led_7, led_6, led_5, led_4, led_3, led_2, led_1, led_0} = counter >> 24;

endmodule
