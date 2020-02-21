// Virtex 2, Virtex 2 Pro, Spartan 3, Spartan 3E, Spartan 3A block RAM
// mapping (Spartan 3A is a superset of the other four).

// ------------------------------------------------------------------------

module \$__XILINX_RAMB16 (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);
	parameter CFG_ABITS = 9;
	parameter CFG_DBITS = 36;
	parameter CFG_ENABLE_B = 1;

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

	generate if (CFG_DBITS == 1) begin
		wire DOB;
		RAMB16_S1_S1 #(
			`include "brams_init_16.vh"
			.WRITE_MODE_A("READ_FIRST"),
			.WRITE_MODE_B("READ_FIRST"),
		) _TECHMAP_REPLACE_ (
			.DIA(1'd0),
			.DOA(A1DATA),
			.ADDRA(A1ADDR),
			.CLKA(CLK2 ^ !CLKPOL2),
			.ENA(A1EN),
			.SSRA(|0),
			.WEA(1'b0),

			.DIB(B1DATA),
			.DOB(DOB),
			.ADDRB(B1ADDR),
			.CLKB(CLK3 ^ !CLKPOL3),
			.ENB(|1),
			.SSRB(|0),
			.WEB(B1EN)
		);
	end else if (CFG_DBITS == 2) begin
		wire [1:0] DOB;
		RAMB16_S2_S2 #(
			`include "brams_init_16.vh"
			.WRITE_MODE_A("READ_FIRST"),
			.WRITE_MODE_B("READ_FIRST"),
		) _TECHMAP_REPLACE_ (
			.DIA(2'd0),
			.DOA(A1DATA),
			.ADDRA(A1ADDR),
			.CLKA(CLK2 ^ !CLKPOL2),
			.ENA(A1EN),
			.SSRA(|0),
			.WEA(1'b0),

			.DIB(B1DATA),
			.DOB(DOB),
			.ADDRB(B1ADDR),
			.CLKB(CLK3 ^ !CLKPOL3),
			.ENB(|1),
			.SSRB(|0),
			.WEB(B1EN)
		);
	end else if (CFG_DBITS == 4) begin
		wire [3:0] DOB;
		RAMB16_S4_S4 #(
			`include "brams_init_16.vh"
			.WRITE_MODE_A("READ_FIRST"),
			.WRITE_MODE_B("READ_FIRST"),
		) _TECHMAP_REPLACE_ (
			.DIA(4'd0),
			.DOA(A1DATA),
			.ADDRA(A1ADDR),
			.CLKA(CLK2 ^ !CLKPOL2),
			.ENA(A1EN),
			.SSRA(|0),
			.WEA(1'b0),

			.DIB(B1DATA),
			.DOB(DOB),
			.ADDRB(B1ADDR),
			.CLKB(CLK3 ^ !CLKPOL3),
			.ENB(|1),
			.SSRB(|0),
			.WEB(B1EN)
		);
	end else if (CFG_DBITS == 9) begin
		wire [7:0] DOB;
		wire DOPB;
		RAMB16_S9_S9 #(
			`include "brams_init_18.vh"
			.WRITE_MODE_A("READ_FIRST"),
			.WRITE_MODE_B("READ_FIRST"),
		) _TECHMAP_REPLACE_ (
			.DIA(8'd0),
			.DIPA(1'd0),
			.DOA(A1DATA[7:0]),
			.DOPA(A1DATA[8]),
			.ADDRA(A1ADDR),
			.CLKA(CLK2 ^ !CLKPOL2),
			.ENA(A1EN),
			.SSRA(|0),
			.WEA(1'b0),

			.DIB(B1DATA[7:0]),
			.DIPB(B1DATA[8]),
			.DOB(DOB),
			.DOPB(DOPB),
			.ADDRB(B1ADDR),
			.CLKB(CLK3 ^ !CLKPOL3),
			.ENB(|1),
			.SSRB(|0),
			.WEB(B1EN)
		);
	end else if (CFG_DBITS == 18) begin
		wire [15:0] DOB;
		wire [1:0] DOPB;
		RAMB16_S18_S18 #(
			`include "brams_init_18.vh"
			.WRITE_MODE_A("READ_FIRST"),
			.WRITE_MODE_B("READ_FIRST"),
		) _TECHMAP_REPLACE_ (
			.DIA(16'd0),
			.DIPA(2'd0),
			.DOA({A1DATA[16:9], A1DATA[7:0]}),
			.DOPA({A1DATA[17], A1DATA[8]}),
			.ADDRA(A1ADDR),
			.CLKA(CLK2 ^ !CLKPOL2),
			.ENA(A1EN),
			.SSRA(|0),
			.WEA(1'b0),

			.DIB({B1DATA[16:9], B1DATA[7:0]}),
			.DIPB({B1DATA[17], B1DATA[8]}),
			.DOB(DOB),
			.DOPB(DOPB),
			.ADDRB(B1ADDR),
			.CLKB(CLK3 ^ !CLKPOL3),
			.ENB(|1),
			.SSRB(|0),
			.WEB(B1EN)
		);
	end else if (CFG_DBITS == 36) begin
		wire [31:0] DOB;
		wire [3:0] DOPB;
		RAMB16_S36_S36 #(
			`include "brams_init_18.vh"
			.WRITE_MODE_A("READ_FIRST"),
			.WRITE_MODE_B("READ_FIRST"),
		) _TECHMAP_REPLACE_ (
			.DIA(32'd0),
			.DIPA(4'd0),
			.DOA({A1DATA[34:27], A1DATA[25:18], A1DATA[16:9], A1DATA[7:0]}),
			.DOPA({A1DATA[35], A1DATA[26], A1DATA[17], A1DATA[8]}),
			.ADDRA(A1ADDR),
			.CLKA(CLK2 ^ !CLKPOL2),
			.ENA(A1EN),
			.SSRA(|0),
			.WEA(1'b0),

			.DIB({B1DATA[34:27], B1DATA[25:18], B1DATA[16:9], B1DATA[7:0]}),
			.DIPB({B1DATA[35], B1DATA[26], B1DATA[17], B1DATA[8]}),
			.DOB(DOB),
			.DOPB(DOPB),
			.ADDRB(B1ADDR),
			.CLKB(CLK3 ^ !CLKPOL3),
			.ENB(|1),
			.SSRB(|0),
			.WEB(B1EN)
		);
	end else begin
		$error("Strange block RAM data width.");
	end endgenerate
endmodule


// Version with separate byte enables, only available on Spartan 3A.

module \$__XILINX_RAMB16BWE (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);
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

	generate if (CFG_DBITS == 18) begin
		wire [15:0] DOB;
		wire [1:0] DOPB;
		RAMB16BWE_S18_S18 #(
			`include "brams_init_18.vh"
			.WRITE_MODE_A("READ_FIRST"),
			.WRITE_MODE_B("READ_FIRST"),
		) _TECHMAP_REPLACE_ (
			.DIA(16'd0),
			.DIPA(2'd0),
			.DOA({A1DATA[16:9], A1DATA[7:0]}),
			.DOPA({A1DATA[17], A1DATA[8]}),
			.ADDRA(A1ADDR),
			.CLKA(CLK2 ^ !CLKPOL2),
			.ENA(A1EN),
			.SSRA(|0),
			.WEA(2'b00),

			.DIB({B1DATA[16:9], B1DATA[7:0]}),
			.DIPB({B1DATA[17], B1DATA[8]}),
			.DOB(DOB),
			.DOPB(DOPB),
			.ADDRB(B1ADDR),
			.CLKB(CLK3 ^ !CLKPOL3),
			.ENB(|1),
			.SSRB(|0),
			.WEB(B1EN)
		);
	end else if (CFG_DBITS == 36) begin
		wire [31:0] DOB;
		wire [3:0] DOPB;
		RAMB16BWE_S36_S36 #(
			`include "brams_init_18.vh"
			.WRITE_MODE_A("READ_FIRST"),
			.WRITE_MODE_B("READ_FIRST"),
		) _TECHMAP_REPLACE_ (
			.DIA(32'd0),
			.DIPA(4'd0),
			.DOA({A1DATA[34:27], A1DATA[25:18], A1DATA[16:9], A1DATA[7:0]}),
			.DOPA({A1DATA[35], A1DATA[26], A1DATA[17], A1DATA[8]}),
			.ADDRA(A1ADDR),
			.CLKA(CLK2 ^ !CLKPOL2),
			.ENA(A1EN),
			.SSRA(|0),
			.WEA(4'b0000),

			.DIB({B1DATA[34:27], B1DATA[25:18], B1DATA[16:9], B1DATA[7:0]}),
			.DIPB({B1DATA[35], B1DATA[26], B1DATA[17], B1DATA[8]}),
			.DOB(DOB),
			.DOPB(DOPB),
			.ADDRB(B1ADDR),
			.CLKB(CLK3 ^ !CLKPOL3),
			.ENB(|1),
			.SSRB(|0),
			.WEB(B1EN)
		);
	end else begin
		$error("Strange block RAM data width.");
	end endgenerate
endmodule
