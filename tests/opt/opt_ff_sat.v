module top (
	input clk,
	output reg [7:0] cnt
);
	initial cnt = 0;
	always @(posedge clk) begin
		if (cnt < 20)
			cnt <= cnt + 1;
		else
			cnt <= 0;
	end
endmodule
