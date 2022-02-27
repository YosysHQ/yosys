module $__ANLOGIC_DRAM16X4_ (...);
	parameter INIT = 64'b0;

	input PORT_W_CLK;
	input [3:0] PORT_W_ADDR;
	input [3:0] PORT_W_WR_DATA;
	input PORT_W_WR_EN;

	input [3:0] PORT_R_ADDR;
	output [3:0] PORT_R_RD_DATA;

	function [15:0] init_slice;
		input integer idx;
		integer i;
		for (i = 0; i < 16; i = i + 1)
			init_slice[i] = INIT[i * 4 + idx];
	endfunction

	EG_LOGIC_DRAM16X4 #(
		.INIT_D0(init_slice(0)),
		.INIT_D1(init_slice(1)),
		.INIT_D2(init_slice(2)),
		.INIT_D3(init_slice(3))
	) _TECHMAP_REPLACE_ (
		.di(PORT_W_WR_DATA),
		.waddr(PORT_W_ADDR),
		.wclk(PORT_W_CLK),
		.we(PORT_W_WR_EN),
		.raddr(PORT_R_ADDR),
		.do(PORT_R_RD_DATA)
	);
endmodule
