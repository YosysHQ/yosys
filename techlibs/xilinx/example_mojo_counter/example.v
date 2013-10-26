module top(clk, led_7, led_6, led_5, led_4, led_3, led_2, led_1, led_0);

input clk;
output led_7, led_6, led_5, led_4;
output led_3, led_2, led_1, led_0;

reg [31:0] counter;

always @(posedge clk)
	counter <= 32'b_1010_1010_1010_1010_1010_1010_1010_1010; // counter + 1;

assign {led_7, led_6, led_5, led_4, led_3, led_2, led_1, led_0} = counter >> 24;

endmodule
