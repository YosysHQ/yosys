
// `define ASYNC_RESET

module fsm_test(clk, reset, button_a, button_b, red_a, green_a, red_b, green_b);

input clk, reset, button_a, button_b;
output reg red_a, green_a, red_b, green_b;

(* gentb_constant = 0 *)
wire reset;

integer state;
reg [3:0] cnt;

`ifdef ASYNC_RESET
always @(posedge clk, posedge reset)
`else
always @(posedge clk)
`endif
begin
	cnt <= 0;
	red_a <= 1;
	red_b <= 1;
	green_a <= 0;
	green_b <= 0;

	if (reset)
		state <= 100;
	else
		case (state)
			100: begin
				if (button_a && !button_b)
					state <= 200;
				if (!button_a && button_b)
					state <= 300;
			end
			200: begin
				red_a <= 0;
				green_a <= 1;
				cnt <= cnt + 1;
				if (cnt == 5)
					state <= 210;
			end
			210: begin
				red_a <= 0;
				green_a <= cnt[0];
				cnt <= cnt + 1;
				if (cnt == 10)
					state <= 100;
			end
			300: begin
				red_b <= 0;
				green_b <= 1;
				cnt <= cnt + 1;
				if (cnt == 5)
					state <= 310;
			end
			310: begin
				red_b <= 0;
				green_b <= cnt[0];
				cnt <= cnt + 1;
				if (cnt == 10)
					state <= 100;
			end
		endcase
end

endmodule

