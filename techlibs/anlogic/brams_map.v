module \$__ANLOGIC_BRAM9K_TDP (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);
	parameter CFG_ABITS = 10;
	parameter CFG_DBITS = 9;

	parameter CLKPOL2 = 1;
	parameter CLKPOL3 = 1;
	parameter [9215:0] INIT = 9216'bx;
	parameter TRANSP2 = 0;

	input CLK2;
	input CLK3;

	input [CFG_ABITS-1:0] A1ADDR;
	output [CFG_DBITS-1:0] A1DATA;
	input A1EN;

	input [CFG_ABITS-1:0] B1ADDR;
	input [CFG_DBITS-1:0] B1DATA;
	input B1EN;

	localparam CLKAMUX = CLKPOL2 ? "SIG" : "INV";
	localparam CLKBMUX = CLKPOL3 ? "SIG" : "INV";

	localparam WRITEMODE_B = TRANSP2 ? "WRITETHROUGH" : "READBEFOREWRITE";

	localparam DATA_WIDTH = CFG_DBITS == 1 ? "1" :
				(CFG_DBITS == 2 ? "2" :
				 (CFG_DBITS <= 4 ? "4" : "9"));

	localparam APADBITS = $clog2(CFG_DBITS == 9 ? 8 : CFG_DBITS);

	wire [12:0] addra;
	wire [12:0] addrb;

	assign addra[12:APADBITS] = A1ADDR;
	assign addrb[12:APADBITS] = B1ADDR;

	wire [8:0] doa;
	wire [8:0] dib;

	assign A1DATA[CFG_DBITS-1:0] = doa;
	assign dib[CFG_DBITS-1:0] = B1DATA;

	generate if (CFG_DBITS == 9) begin
		EG_PHY_BRAM #(
			.MODE("DP8K"),
			.DATA_WIDTH_A(DATA_WIDTH),
			.DATA_WIDTH_B(DATA_WIDTH),
			.READBACK("OFF"),
			.REGMODE_A("NOREG"),
			.REGMODE_B("NOREG"),
			.WRITEMODE_A("READBEFOREWRITE"),
			.WRITEMODE_B(WRITEMODE_B),
			.RESETMODE("ASYNC"),
			.CEAMUX("SIG"), .CEBMUX("SIG"),
			.OCEAMUX("1"), .OCEBMUX("1"),
			.RSTAMUX("0"), .RSTBMUX("0"),
			.CLKAMUX(CLKAMUX),
			.CLKBMUX(CLKBMUX),
			.WEAMUX("0"), .WEBMUX("SIG"),
			.CSA0("1"), .CSA1("1"),
			.CSA2("1"), .CSB0("1"),
			.CSB1("1"), .CSB2("1"),
			`include "brams_init_9.vh"
		) _TECHMAP_REPLACE_ (
			.doa(doa), .dib(dib),
			.addra(addra), .addrb(addrb),
			.clka(CLK2), .clkb(CLK3),
			.cea(A1EN), .ceb(B1EN),
			.ocea(1'b1), .oceb(1'b1),
			.rsta(1'b0), .rstb(1'b0),
			.wea(1'b0), .web(B1EN),
			.csa(3'b111), .csb(3'b111)
		);
	end else begin
		EG_PHY_BRAM #(
			.MODE("DP8K"),
			.DATA_WIDTH_A(DATA_WIDTH),
			.DATA_WIDTH_B(DATA_WIDTH),
			.READBACK("OFF"),
			.REGMODE_A("NOREG"),
			.REGMODE_B("NOREG"),
			.WRITEMODE_A("READBEFOREWRITE"),
			.WRITEMODE_B(WRITEMODE_B),
			.RESETMODE("ASYNC"),
			.CEAMUX("SIG"), .CEBMUX("SIG"),
			.OCEAMUX("1"), .OCEBMUX("1"),
			.RSTAMUX("0"), .RSTBMUX("0"),
			.CLKAMUX(CLKAMUX),
			.CLKBMUX(CLKBMUX),
			.WEAMUX("0"), .WEBMUX("SIG"),
			.CSA0("1"), .CSA1("1"),
			.CSA2("1"), .CSB0("1"),
			.CSB1("1"), .CSB2("1"),
			`include "brams_init_8.vh"
		) _TECHMAP_REPLACE_ (
			.doa(doa), .dib(dib),
			.addra(addra), .addrb(addrb),
			.clka(CLK2), .clkb(CLK3),
			.cea(A1EN), .ceb(B1EN),
			.ocea(1'b1), .oceb(1'b1),
			.rsta(1'b0), .rstb(1'b0),
			.wea(1'b0), .web(B1EN),
			.csa(3'b111), .csb(3'b111)
		);
	end endgenerate
endmodule

module \$__ANLOGIC_BRAM32K (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);
	parameter CFG_ABITS = 11;
	parameter CFG_DBITS = 16;

	parameter CLKPOL2 = 1;
	parameter CLKPOL3 = 1;
	parameter [32767:0] INIT = 32768'bx;

	input CLK2;
	input CLK3;

	input [CFG_ABITS-1:0] A1ADDR;
	output [CFG_DBITS-1:0] A1DATA;
	input A1EN;

	input [CFG_ABITS-1:0] B1ADDR;
	input [CFG_DBITS-1:0] B1DATA;
	input [1:0] B1EN;

	localparam CLKAMUX = CLKPOL2 ? "SIG" : "INV";
	localparam CLKBMUX = CLKPOL3 ? "SIG" : "INV";

	wire byteweb = B1EN[1] ^ B1EN[0];
	wire byteb = B1EN[1];

	EG_PHY_BRAM32K #(
		.MODE("DP16K"),
		.DATA_WIDTH_A("16"),
		.DATA_WIDTH_B("16"),
		.REGMODE_A("NOREG"),
		.REGMODE_B("NOREG"),
		.WRITEMODE_A("NORMAL"),
		.WRITEMODE_B("NORMAL"),
		.SRMODE("ASYNC"),
		.CSAMUX("SIG"), .CSBMUX("SIG"),
		.OCEAMUX("1"), .OCEBMUX("1"),
		.RSTAMUX("0"), .RSTBMUX("0"),
		.CLKAMUX(CLKAMUX),
		.CLKBMUX(CLKBMUX),
		.WEAMUX("0"), .WEBMUX("SIG"),
		.READBACK("OFF"),
		`include "brams_init_16.vh"
	) _TECHMAP_REPLACE_ (
		.doa(A1DATA), .dib(B1DATA),
		.addra(A1ADDR), .addrb(B1ADDR),
		.bytea(1'b0), .byteb(byteb),
		.bytewea(1'b0), .byteweb(byteweb),
		.csa(A1EN), .csb(|B1EN),
		.wea(1'b0), .web(|B1EN),
		.clka(CLK2), .clkb(CLK3),
		.rsta(1'b0), .rstb(1'b0),
		.ocea(1'b1), .oceb(1'b1)
	);
endmodule
