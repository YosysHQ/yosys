module \$__NX_PDPSC512K (CLK2, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);
	parameter CFG_ABITS = 14;
	parameter CFG_DBITS = 32;
	parameter CFG_ENABLE_A = 4;

	parameter CLKPOL2 = 1;
	parameter [524287:0] INIT = 524287'b0;

	input CLK2;

	input [CFG_ABITS-1:0] A1ADDR;
	input [CFG_DBITS-1:0] A1DATA;
	input [CFG_ENABLE_A-1:0] A1EN;

	input [CFG_ABITS-1:0] B1ADDR;
	output [CFG_DBITS-1:0] B1DATA;
	input B1EN;

	wire clk;
	wire [31:0] rd;
	assign B1DATA = rd[CFG_DBITS-1:0];

	generate
		if (CLKPOL2)
			assign clk = CLK2;
		else
			INV clk_inv_i (.A(CLK2), .Z(clk));
	endgenerate

	wire we = |A1EN;

	localparam INIT_CHUNK_SIZE = 4096;

	function [5119:0] permute_init;
		input [INIT_CHUNK_SIZE-1:0] chunk;
		integer i;
		begin
			for (i = 0; i < 128; i = i + 1'b1)
				permute_init[i * 40 +: 40] = {8'b0, chunk[i * 32 +: 32]};
		end
	endfunction

	generate
		PDPSC512K #(
			.OUTREG("NO_REG"),
			.ECC_BYTE_SEL("BYTE_EN"),
`include "lrams_init.vh"
			.GSR("DISABLED")
		) _TECHMAP_REPLACE_ (
			.CLK(clk), .RSTR(1'b0),
			.DI(A1DATA), .ADW(A1ADDR), .CEW(we), .WE(we), .CSW(1'b1),
			.ADR(B1ADDR), .DO(rd), .CER(B1EN), .CSR(1'b1),
		);
	endgenerate

endmodule
