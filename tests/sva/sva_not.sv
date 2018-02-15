module top (
	input clk,
	input reset,
	input ping,
	input [1:0] cfg,
	output reg pong
);
	reg [2:0] cnt;
	localparam integer maxdelay = 8;

	always @(posedge clk) begin
		if (reset) begin
			cnt <= 0;
			pong <= 0;
		end else begin
			cnt <= cnt - |cnt;
			pong <= cnt == 1;
			if (ping) cnt <= 4 + cfg;
		end
	end

	assert property (
		@(posedge clk)
		disable iff (reset)
		not (ping ##1 !pong [*maxdelay])
	);

`ifndef FAIL
	assume property (
		@(posedge clk)
		not (cnt && ping)
	);
`endif
endmodule
