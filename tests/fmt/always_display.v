module m(input clk, rst, en, input [31:0] data);

`ifdef EVENT_CLK
	always @(posedge clk)
`endif
`ifdef EVENT_CLK_RST
	always @(posedge clk or negedge rst)
`endif
`ifdef EVENT_STAR
	always @(*)
`endif
`ifdef COND_EN
		if (en)
`endif
			$display("data=%d", data);

endmodule
