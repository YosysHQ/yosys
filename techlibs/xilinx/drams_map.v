
module \$__XILINX_RAM32X1D (CLK1, A1ADDR, A1DATA, B1ADDR, B1DATA, B1EN);
	parameter [31:0] INIT = 32'bx;
	parameter CLKPOL2 = 1;
	input CLK1;

	input [4:0] A1ADDR;
	output A1DATA;

	input [4:0] B1ADDR;
	input B1DATA;
	input B1EN;

	RAM32X1D #(
		.INIT(INIT),
		.IS_WCLK_INVERTED(!CLKPOL2)
	) _TECHMAP_REPLACE_ (
		.DPRA0(A1ADDR[0]),
		.DPRA1(A1ADDR[1]),
		.DPRA2(A1ADDR[2]),
		.DPRA3(A1ADDR[3]),
		.DPRA4(A1ADDR[4]),
		.DPO(A1DATA),

		.A0(B1ADDR[0]),
		.A1(B1ADDR[1]),
		.A2(B1ADDR[2]),
		.A3(B1ADDR[3]),
		.A4(B1ADDR[4]),
		.D(B1DATA),
		.WCLK(CLK1),
		.WE(B1EN)
	);
endmodule

