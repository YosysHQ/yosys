module top (input clk, reset, up, down, output reg [7:0] cnt);
	always @(posedge clk) begin
		if (reset)
			cnt <= 0;
		else if (up)
			cnt <= cnt + 1;
		else if (down)
			cnt <= cnt - 1;
	end

	default clocking @(posedge clk); endclocking
	default disable iff (reset);

	assert property (up |=> cnt == $past(cnt) + 8'd 1);
	assert property (up [*2] |=> cnt == $past(cnt, 2) + 8'd 2);
	assert property (up ##1 up |=> cnt == $past(cnt, 2) + 8'd 2);

`ifndef FAIL
	assume property (down |-> !up);
`endif
	assert property (up ##1 down |=> cnt == $past(cnt, 2));
	assert property (down |=> cnt == $past(cnt) - 8'd 1);

	property down_n(n);
		down [*n] |=> cnt == $past(cnt, n) - n;
	endproperty

	assert property (down_n(8'd 3));
	assert property (down_n(8'd 5));
endmodule
