// Ultrascale and Ultrascale Plus block RAM mapping.

module \$__XILINX_RAMB36_SDP (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);
	parameter CLKPOL2 = 1;
	parameter CLKPOL3 = 1;
	parameter [36863:0] INIT = 36864'bx;

	input CLK2;
	input CLK3;

	input [8:0] A1ADDR;
	output [71:0] A1DATA;
	input A1EN;

	input [8:0] B1ADDR;
	input [71:0] B1DATA;
	input [7:0] B1EN;

	wire [15:0] A1ADDR_16 = {A1ADDR, 6'b0};
	wire [15:0] B1ADDR_16 = {B1ADDR, 6'b0};

	wire [7:0] DIP, DOP;
	wire [63:0] DI, DO;

	assign A1DATA = { DOP[7], DO[63:56], DOP[6], DO[55:48], DOP[5], DO[47:40], DOP[4], DO[39:32],
	                  DOP[3], DO[31:24], DOP[2], DO[23:16], DOP[1], DO[15: 8], DOP[0], DO[ 7: 0] };

	assign { DIP[7], DI[63:56], DIP[6], DI[55:48], DIP[5], DI[47:40], DIP[4], DI[39:32],
	         DIP[3], DI[31:24], DIP[2], DI[23:16], DIP[1], DI[15: 8], DIP[0], DI[ 7: 0] } = B1DATA;

	RAMB36E2 #(
		.READ_WIDTH_A(72),
		.WRITE_WIDTH_B(72),
		.WRITE_MODE_A("READ_FIRST"),
		.WRITE_MODE_B("READ_FIRST"),
		.DOA_REG(0),
		.DOB_REG(0),
		.IS_CLKARDCLK_INVERTED(!CLKPOL2),
		.IS_CLKBWRCLK_INVERTED(!CLKPOL3),
		`include "brams_init_36.vh"
	) _TECHMAP_REPLACE_ (
		.DOUTBDOUT(DO[63:32]),
		.DOUTADOUT(DO[31:0]),
		.DOUTPBDOUTP(DOP[7:4]),
		.DOUTPADOUTP(DOP[3:0]),
		.DINBDIN(DI[63:32]),
		.DINADIN(DI[31:0]),
		.DINPBDINP(DIP[7:4]),
		.DINPADINP(DIP[3:0]),

		.ADDRARDADDR(A1ADDR_16),
		.CLKARDCLK(CLK2),
		.ENARDEN(A1EN),
		.ADDRENA(|1),
		.REGCEAREGCE(|1),
		.RSTRAMARSTRAM(|0),
		.RSTREGARSTREG(|0),
		.WEA(4'b0),

		.ADDRBWRADDR(B1ADDR_16),
		.CLKBWRCLK(CLK3),
		.ENBWREN(|1),
		.ADDRENB(|1),
		.REGCEB(|1),
		.RSTRAMB(|0),
		.RSTREGB(|0),
		.WEBWE(B1EN),

		.SLEEP(|0)
	);
endmodule

// ------------------------------------------------------------------------

module \$__XILINX_RAMB18_SDP (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);
	parameter CLKPOL2 = 1;
	parameter CLKPOL3 = 1;
	parameter [18431:0] INIT = 18432'bx;

	input CLK2;
	input CLK3;

	input [8:0] A1ADDR;
	output [35:0] A1DATA;
	input A1EN;

	input [8:0] B1ADDR;
	input [35:0] B1DATA;
	input [3:0] B1EN;

	wire [13:0] A1ADDR_14 = {A1ADDR, 5'b0};
	wire [13:0] B1ADDR_14 = {B1ADDR, 5'b0};

	wire [3:0] DIP, DOP;
	wire [31:0] DI, DO;

	assign A1DATA = { DOP[3], DO[31:24], DOP[2], DO[23:16], DOP[1], DO[15: 8], DOP[0], DO[ 7: 0] };
	assign { DIP[3], DI[31:24], DIP[2], DI[23:16], DIP[1], DI[15: 8], DIP[0], DI[ 7: 0] } = B1DATA;

	RAMB18E2 #(
		.READ_WIDTH_A(36),
		.WRITE_WIDTH_B(36),
		.WRITE_MODE_A("READ_FIRST"),
		.WRITE_MODE_B("READ_FIRST"),
		.DOA_REG(0),
		.DOB_REG(0),
		.IS_CLKARDCLK_INVERTED(!CLKPOL2),
		.IS_CLKBWRCLK_INVERTED(!CLKPOL3),
		`include "brams_init_18.vh"
	) _TECHMAP_REPLACE_ (
		.DOUTBDOUT(DO[31:16]),
		.DOUTADOUT(DO[15:0]),
		.DOUTPBDOUTP(DOP[3:2]),
		.DOUTPADOUTP(DOP[1:0]),
		.DINBDIN(DI[31:16]),
		.DINADIN(DI[15:0]),
		.DINPBDINP(DIP[3:2]),
		.DINPADINP(DIP[1:0]),

		.ADDRARDADDR(A1ADDR_14),
		.CLKARDCLK(CLK2),
		.ENARDEN(A1EN),
		.ADDRENA(|1),
		.REGCEAREGCE(|1),
		.RSTRAMARSTRAM(|0),
		.RSTREGARSTREG(|0),
		.WEA(2'b0),

		.ADDRBWRADDR(B1ADDR_14),
		.CLKBWRCLK(CLK3),
		.ENBWREN(|1),
		.ADDRENB(|1),
		.REGCEB(|1),
		.RSTRAMB(|0),
		.RSTREGB(|0),
		.WEBWE(B1EN),

		.SLEEP(|0)
	);
endmodule

// ------------------------------------------------------------------------

module \$__XILINX_RAMB36_TDP (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);
	parameter CFG_ABITS = 10;
	parameter CFG_DBITS = 36;
	parameter CFG_ENABLE_B = 4;

	parameter CLKPOL2 = 1;
	parameter CLKPOL3 = 1;
	parameter [36863:0] INIT = 36864'bx;

	input CLK2;
	input CLK3;

	input [CFG_ABITS-1:0] A1ADDR;
	output [CFG_DBITS-1:0] A1DATA;
	input A1EN;

	input [CFG_ABITS-1:0] B1ADDR;
	input [CFG_DBITS-1:0] B1DATA;
	input [CFG_ENABLE_B-1:0] B1EN;

	wire [15:0] A1ADDR_16 = A1ADDR << (15 - CFG_ABITS);
	wire [15:0] B1ADDR_16 = B1ADDR << (15 - CFG_ABITS);
	wire [7:0] B1EN_8 = B1EN;

	wire [3:0] DIP, DOP;
	wire [31:0] DI, DO;

	wire [31:0] DOBDO;
	wire [3:0] DOPBDOP;

	assign A1DATA = { DOP[3], DO[31:24], DOP[2], DO[23:16], DOP[1], DO[15: 8], DOP[0], DO[ 7: 0] };
	assign { DIP[3], DI[31:24], DIP[2], DI[23:16], DIP[1], DI[15: 8], DIP[0], DI[ 7: 0] } = B1DATA;

	generate if (CFG_DBITS > 8) begin
		RAMB36E2 #(
			.READ_WIDTH_A(CFG_DBITS),
			.READ_WIDTH_B(CFG_DBITS),
			.WRITE_WIDTH_A(CFG_DBITS),
			.WRITE_WIDTH_B(CFG_DBITS),
			.WRITE_MODE_A("READ_FIRST"),
			.WRITE_MODE_B("READ_FIRST"),
			.DOA_REG(0),
			.DOB_REG(0),
			.IS_CLKARDCLK_INVERTED(!CLKPOL2),
			.IS_CLKBWRCLK_INVERTED(!CLKPOL3),
			`include "brams_init_36.vh"
		) _TECHMAP_REPLACE_ (
			.DINADIN(32'hFFFFFFFF),
			.DINPADINP(4'hF),
			.DOUTADOUT(DO[31:0]),
			.DOUTPADOUTP(DOP[3:0]),
			.ADDRARDADDR(A1ADDR_16),
			.CLKARDCLK(CLK2),
			.ENARDEN(A1EN),
			.ADDRENA(|1),
			.REGCEAREGCE(|1),
			.RSTRAMARSTRAM(|0),
			.RSTREGARSTREG(|0),
			.WEA(4'b0),

			.DINBDIN(DI),
			.DINPBDINP(DIP),
			.DOUTBDOUT(DOBDO),
			.DOUTPBDOUTP(DOPBDOP),
			.ADDRBWRADDR(B1ADDR_16),
			.CLKBWRCLK(CLK3),
			.ENBWREN(|1),
			.ADDRENB(|1),
			.REGCEB(|0),
			.RSTRAMB(|0),
			.RSTREGB(|0),
			.WEBWE(B1EN_8),

			.SLEEP(|0)
		);
	end else begin
		RAMB36E2 #(
			.READ_WIDTH_A(CFG_DBITS),
			.READ_WIDTH_B(CFG_DBITS),
			.WRITE_WIDTH_A(CFG_DBITS),
			.WRITE_WIDTH_B(CFG_DBITS),
			.WRITE_MODE_A("READ_FIRST"),
			.WRITE_MODE_B("READ_FIRST"),
			.DOA_REG(0),
			.DOB_REG(0),
			.IS_CLKARDCLK_INVERTED(!CLKPOL2),
			.IS_CLKBWRCLK_INVERTED(!CLKPOL3),
			`include "brams_init_32.vh"
		) _TECHMAP_REPLACE_ (
			.DINADIN(32'hFFFFFFFF),
			.DINPADINP(4'hF),
			.DOUTADOUT(DO[31:0]),
			.DOUTPADOUTP(DOP[3:0]),
			.ADDRARDADDR(A1ADDR_16),
			.CLKARDCLK(CLK2),
			.ENARDEN(A1EN),
			.ADDRENA(|1),
			.REGCEAREGCE(|1),
			.RSTRAMARSTRAM(|0),
			.RSTREGARSTREG(|0),
			.WEA(4'b0),

			.DINBDIN(DI),
			.DINPBDINP(DIP),
			.DOUTBDOUT(DOBDO),
			.DOUTPBDOUTP(DOPBDOP),
			.ADDRBWRADDR(B1ADDR_16),
			.CLKBWRCLK(CLK3),
			.ENBWREN(|1),
			.ADDRENB(|1),
			.REGCEB(|0),
			.RSTRAMB(|0),
			.RSTREGB(|0),
			.WEBWE(B1EN_8),

			.SLEEP(|0)
		);
	end endgenerate
endmodule

// ------------------------------------------------------------------------

module \$__XILINX_RAMB18_TDP (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);
	parameter CFG_ABITS = 10;
	parameter CFG_DBITS = 18;
	parameter CFG_ENABLE_B = 2;

	parameter CLKPOL2 = 1;
	parameter CLKPOL3 = 1;
	parameter [18431:0] INIT = 18432'bx;

	input CLK2;
	input CLK3;

	input [CFG_ABITS-1:0] A1ADDR;
	output [CFG_DBITS-1:0] A1DATA;
	input A1EN;

	input [CFG_ABITS-1:0] B1ADDR;
	input [CFG_DBITS-1:0] B1DATA;
	input [CFG_ENABLE_B-1:0] B1EN;

	wire [13:0] A1ADDR_14 = A1ADDR << (14 - CFG_ABITS);
	wire [13:0] B1ADDR_14 = B1ADDR << (14 - CFG_ABITS);
	wire [3:0] B1EN_4 = B1EN;

	wire [1:0] DIP, DOP;
	wire [15:0] DI, DO;

	wire [15:0] DOBDO;
	wire [1:0] DOPBDOP;

	assign A1DATA = { DOP[1], DO[15: 8], DOP[0], DO[ 7: 0] };
	assign { DIP[1], DI[15: 8], DIP[0], DI[ 7: 0] } = B1DATA;

	generate if (CFG_DBITS > 8) begin
		RAMB18E2 #(
			.READ_WIDTH_A(CFG_DBITS),
			.READ_WIDTH_B(CFG_DBITS),
			.WRITE_WIDTH_A(CFG_DBITS),
			.WRITE_WIDTH_B(CFG_DBITS),
			.WRITE_MODE_A("READ_FIRST"),
			.WRITE_MODE_B("READ_FIRST"),
			.DOA_REG(0),
			.DOB_REG(0),
			.IS_CLKARDCLK_INVERTED(!CLKPOL2),
			.IS_CLKBWRCLK_INVERTED(!CLKPOL3),
			`include "brams_init_18.vh"
		) _TECHMAP_REPLACE_ (
			.DINADIN(16'hFFFF),
			.DINPADINP(2'b11),
			.DOUTADOUT(DO),
			.DOUTPADOUTP(DOP),
			.ADDRARDADDR(A1ADDR_14),
			.CLKARDCLK(CLK2),
			.ENARDEN(A1EN),
			.ADDRENA(|1),
			.REGCEAREGCE(|1),
			.RSTRAMARSTRAM(|0),
			.RSTREGARSTREG(|0),
			.WEA(2'b0),

			.DINBDIN(DI),
			.DINPBDINP(DIP),
			.DOUTBDOUT(DOBDO),
			.DOUTPBDOUTP(DOPBDOP),
			.ADDRBWRADDR(B1ADDR_14),
			.CLKBWRCLK(CLK3),
			.ENBWREN(|1),
			.ADDRENB(|1),
			.REGCEB(|0),
			.RSTRAMB(|0),
			.RSTREGB(|0),
			.WEBWE(B1EN_4),

			.SLEEP(|0)
		);
	end else begin
		RAMB18E2 #(
			//.RAM_MODE("TDP"),
			.READ_WIDTH_A(CFG_DBITS),
			.READ_WIDTH_B(CFG_DBITS),
			.WRITE_WIDTH_A(CFG_DBITS),
			.WRITE_WIDTH_B(CFG_DBITS),
			.WRITE_MODE_A("READ_FIRST"),
			.WRITE_MODE_B("READ_FIRST"),
			.DOA_REG(0),
			.DOB_REG(0),
			.IS_CLKARDCLK_INVERTED(!CLKPOL2),
			.IS_CLKBWRCLK_INVERTED(!CLKPOL3),
			`include "brams_init_16.vh"
		) _TECHMAP_REPLACE_ (
			.DINADIN(16'hFFFF),
			.DINPADINP(2'b11),
			.DOUTADOUT(DO),
			.DOUTPADOUTP(DOP),
			.ADDRARDADDR(A1ADDR_14),
			.CLKARDCLK(CLK2),
			.ENARDEN(A1EN),
			.ADDRENA(|1),
			.REGCEAREGCE(|1),
			.RSTRAMARSTRAM(|0),
			.RSTREGARSTREG(|0),
			.WEA(2'b0),

			.DINBDIN(DI),
			.DINPBDINP(DIP),
			.DOUTBDOUT(DOBDO),
			.DOUTPBDOUTP(DOPBDOP),
			.ADDRBWRADDR(B1ADDR_14),
			.CLKBWRCLK(CLK3),
			.ENBWREN(|1),
			.ADDRENB(|1),
			.REGCEB(|0),
			.RSTRAMB(|0),
			.RSTREGB(|0),
			.WEBWE(B1EN_4),

			.SLEEP(|0)
		);
	end endgenerate
endmodule

