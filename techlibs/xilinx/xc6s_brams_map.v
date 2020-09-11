// Spartan 3A DSP and Spartan 6 block RAM mapping (Spartan 6 is a superset of
// Spartan 3A DSP).

module \$__XILINX_RAMB8BWER_SDP (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);
	parameter CLKPOL2 = 1;
	parameter CLKPOL3 = 1;
	parameter [9215:0] INIT = 9216'bx;

	input CLK2;
	input CLK3;

	input [7:0] A1ADDR;
	output [35:0] A1DATA;
	input A1EN;

	input [7:0] B1ADDR;
	input [35:0] B1DATA;
	input [3:0] B1EN;

	wire [12:0] A1ADDR_13 = {A1ADDR, 5'b0};
	wire [12:0] B1ADDR_13 = {B1ADDR, 5'b0};

	wire [3:0] DIP, DOP;
	wire [31:0] DI, DO;

	assign A1DATA = { DOP[3], DO[31:24], DOP[2], DO[23:16], DOP[1], DO[15: 8], DOP[0], DO[ 7: 0] };
	assign { DIP[3], DI[31:24], DIP[2], DI[23:16], DIP[1], DI[15: 8], DIP[0], DI[ 7: 0] } = B1DATA;

	RAMB8BWER #(
		.RAM_MODE("SDP"),
		.DATA_WIDTH_A(36),
		.DATA_WIDTH_B(36),
		.WRITE_MODE_A("READ_FIRST"),
		.WRITE_MODE_B("READ_FIRST"),
		`include "brams_init_9.vh"
	) _TECHMAP_REPLACE_ (
		.DOBDO(DO[31:16]),
		.DOADO(DO[15:0]),
		.DOPBDOP(DOP[3:2]),
		.DOPADOP(DOP[1:0]),
		.DIBDI(DI[31:16]),
		.DIADI(DI[15:0]),
		.DIPBDIP(DIP[3:2]),
		.DIPADIP(DIP[1:0]),
		.WEBWEU(B1EN[3:2]),
		.WEAWEL(B1EN[1:0]),

		.ADDRAWRADDR(B1ADDR_13),
		.CLKAWRCLK(CLK3 ^ !CLKPOL3),
		.ENAWREN(|1),
		.REGCEA(|0),
		.RSTA(|0),

		.ADDRBRDADDR(A1ADDR_13),
		.CLKBRDCLK(CLK2 ^ !CLKPOL2),
		.ENBRDEN(A1EN),
		.REGCEBREGCE(|1),
		.RSTBRST(|0)
	);
endmodule

// ------------------------------------------------------------------------

module \$__XILINX_RAMB16BWER_TDP (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);
	parameter CFG_ABITS = 9;
	parameter CFG_DBITS = 36;
	parameter CFG_ENABLE_B = 4;

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
	wire [3:0] B1EN_4 = {4{B1EN}};

	wire [3:0] DIP, DOP;
	wire [31:0] DI, DO;

	wire [31:0] DOB;
	wire [3:0] DOPB;

	assign A1DATA = { DOP[3], DO[31:24], DOP[2], DO[23:16], DOP[1], DO[15: 8], DOP[0], DO[ 7: 0] };
	assign { DIP[3], DI[31:24], DIP[2], DI[23:16], DIP[1], DI[15: 8], DIP[0], DI[ 7: 0] } = B1DATA;

	generate if (CFG_DBITS > 8) begin
		RAMB16BWER #(
			.DATA_WIDTH_A(CFG_DBITS),
			.DATA_WIDTH_B(CFG_DBITS),
			.WRITE_MODE_A("READ_FIRST"),
			.WRITE_MODE_B("READ_FIRST"),
			`include "brams_init_18.vh"
		) _TECHMAP_REPLACE_ (
			.DIA(32'd0),
			.DIPA(4'd0),
			.DOA(DO[31:0]),
			.DOPA(DOP[3:0]),
			.ADDRA(A1ADDR_14),
			.CLKA(CLK2 ^ !CLKPOL2),
			.ENA(A1EN),
			.REGCEA(|1),
			.RSTA(|0),
			.WEA(4'b0),

			.DIB(DI),
			.DIPB(DIP),
			.DOB(DOB),
			.DOPB(DOPB),
			.ADDRB(B1ADDR_14),
			.CLKB(CLK3 ^ !CLKPOL3),
			.ENB(|1),
			.REGCEB(|0),
			.RSTB(|0),
			.WEB(B1EN_4)
		);
	end else begin
		RAMB16BWER #(
			.DATA_WIDTH_A(CFG_DBITS),
			.DATA_WIDTH_B(CFG_DBITS),
			.WRITE_MODE_A("READ_FIRST"),
			.WRITE_MODE_B("READ_FIRST"),
			`include "brams_init_16.vh"
		) _TECHMAP_REPLACE_ (
			.DIA(32'd0),
			.DIPA(4'd0),
			.DOA(DO[31:0]),
			.DOPA(DOP[3:0]),
			.ADDRA(A1ADDR_14),
			.CLKA(CLK2 ^ !CLKPOL2),
			.ENA(A1EN),
			.REGCEA(|1),
			.RSTA(|0),
			.WEA(4'b0),

			.DIB(DI),
			.DIPB(DIP),
			.DOB(DOB),
			.DOPB(DOPB),
			.ADDRB(B1ADDR_14),
			.CLKB(CLK3 ^ !CLKPOL3),
			.ENB(|1),
			.REGCEB(|0),
			.RSTB(|0),
			.WEB(B1EN_4)
		);
	end endgenerate
endmodule

// ------------------------------------------------------------------------

module \$__XILINX_RAMB8BWER_TDP (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);
	parameter CFG_ABITS = 9;
	parameter CFG_DBITS = 18;
	parameter CFG_ENABLE_B = 2;

	parameter CLKPOL2 = 1;
	parameter CLKPOL3 = 1;
	parameter [9215:0] INIT = 9216'bx;

	input CLK2;
	input CLK3;

	input [CFG_ABITS-1:0] A1ADDR;
	output [CFG_DBITS-1:0] A1DATA;
	input A1EN;

	input [CFG_ABITS-1:0] B1ADDR;
	input [CFG_DBITS-1:0] B1DATA;
	input [CFG_ENABLE_B-1:0] B1EN;

	wire [12:0] A1ADDR_13 = A1ADDR << (13 - CFG_ABITS);
	wire [12:0] B1ADDR_13 = B1ADDR << (13 - CFG_ABITS);
	wire [1:0] B1EN_2 = {2{B1EN}};

	wire [1:0] DIP, DOP;
	wire [15:0] DI, DO;

	wire [15:0] DOBDO;
	wire [1:0] DOPBDOP;

	assign A1DATA = { DOP[1], DO[15: 8], DOP[0], DO[ 7: 0] };
	assign { DIP[1], DI[15: 8], DIP[0], DI[ 7: 0] } = B1DATA;

	generate if (CFG_DBITS > 8) begin
		RAMB8BWER #(
			.RAM_MODE("TDP"),
			.DATA_WIDTH_A(CFG_DBITS),
			.DATA_WIDTH_B(CFG_DBITS),
			.WRITE_MODE_A("READ_FIRST"),
			.WRITE_MODE_B("READ_FIRST"),
			`include "brams_init_9.vh"
		) _TECHMAP_REPLACE_ (
			.DIADI(16'b0),
			.DIPADIP(2'b0),
			.DOADO(DO),
			.DOPADOP(DOP),
			.ADDRAWRADDR(A1ADDR_13),
			.CLKAWRCLK(CLK2 ^ !CLKPOL2),
			.ENAWREN(A1EN),
			.REGCEA(|1),
			.RSTA(|0),
			.WEAWEL(2'b0),

			.DIBDI(DI),
			.DIPBDIP(DIP),
			.DOBDO(DOBDO),
			.DOPBDOP(DOPBDOP),
			.ADDRBRDADDR(B1ADDR_13),
			.CLKBRDCLK(CLK3 ^ !CLKPOL3),
			.ENBRDEN(|1),
			.REGCEBREGCE(|0),
			.RSTBRST(|0),
			.WEBWEU(B1EN_2)
		);
	end else begin
		RAMB8BWER #(
			.RAM_MODE("TDP"),
			.DATA_WIDTH_A(CFG_DBITS),
			.DATA_WIDTH_B(CFG_DBITS),
			.WRITE_MODE_A("READ_FIRST"),
			.WRITE_MODE_B("READ_FIRST"),
			`include "brams_init_8.vh"
		) _TECHMAP_REPLACE_ (
			.DIADI(16'b0),
			.DIPADIP(2'b0),
			.DOADO(DO),
			.DOPADOP(DOP),
			.ADDRAWRADDR(A1ADDR_13),
			.CLKAWRCLK(CLK2 ^ !CLKPOL2),
			.ENAWREN(A1EN),
			.REGCEA(|1),
			.RSTA(|0),
			.WEAWEL(2'b0),

			.DIBDI(DI),
			.DIPBDIP(DIP),
			.DOBDO(DOBDO),
			.DOPBDOP(DOPBDOP),
			.ADDRBRDADDR(B1ADDR_13),
			.CLKBRDCLK(CLK3 ^ !CLKPOL3),
			.ENBRDEN(|1),
			.REGCEBREGCE(|0),
			.RSTBRST(|0),
			.WEBWEU(B1EN_2)
		);
	end endgenerate
endmodule
