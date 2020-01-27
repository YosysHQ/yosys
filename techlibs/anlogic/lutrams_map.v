module \$__ANLOGIC_DRAM16X4 (CLK1, A1ADDR, A1DATA, B1ADDR, B1DATA, B1EN);
	parameter [63:0]INIT = 64'bx;
	input CLK1;

	input [3:0] A1ADDR;
	output [3:0] A1DATA;

	input [3:0] B1ADDR;
	input [3:0] B1DATA;
	input B1EN;

	EG_LOGIC_DRAM16X4 #(
		`include "lutram_init_16x4.vh"
	) _TECHMAP_REPLACE_ (
		.di(B1DATA),
		.waddr(B1ADDR),
		.wclk(CLK1),
		.we(B1EN),
		.raddr(A1ADDR),
		.do(A1DATA)
	);
endmodule
