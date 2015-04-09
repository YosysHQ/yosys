
module \$__XILINX_RAM64X1D (CLK1, A1ADDR, A1DATA, B1ADDR, B1DATA, B1EN);
	parameter [63:0] INIT = 64'bx;
	parameter CLKPOL2 = 1;
	input CLK1;

	input [5:0] A1ADDR;
	output A1DATA;

	input [5:0] B1ADDR;
	input B1DATA;
	input B1EN;

	RAM64X1D #(
		.INIT(INIT),
		.IS_WCLK_INVERTED(!CLKPOL2)
	) _TECHMAP_REPLACE_ (
		.DPRA0(A1ADDR[0]),
		.DPRA1(A1ADDR[1]),
		.DPRA2(A1ADDR[2]),
		.DPRA3(A1ADDR[3]),
		.DPRA4(A1ADDR[4]),
		.DPRA5(A1ADDR[5]),
		.DPO(A1DATA),

		.A0(B1ADDR[0]),
		.A1(B1ADDR[1]),
		.A2(B1ADDR[2]),
		.A3(B1ADDR[3]),
		.A4(B1ADDR[4]),
		.A5(B1ADDR[5]),
		.D(B1DATA),
		.WCLK(CLK1),
		.WE(B1EN)
	);
endmodule

module \$__XILINX_RAM128X1D (CLK1, A1ADDR, A1DATA, B1ADDR, B1DATA, B1EN);
	parameter [127:0] INIT = 128'bx;
	parameter CLKPOL2 = 1;
	input CLK1;

	input [6:0] A1ADDR;
	output A1DATA;

	input [6:0] B1ADDR;
	input B1DATA;
	input B1EN;

	RAM128X1D #(
		.INIT(INIT),
		.IS_WCLK_INVERTED(!CLKPOL2)
	) _TECHMAP_REPLACE_ (
		.DPRA(A1ADDR),
		.DPO(A1DATA),

		.A(B1ADDR),
		.D(B1DATA),
		.WCLK(CLK1),
		.WE(B1EN)
	);
endmodule

