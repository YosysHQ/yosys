module \$__NX_PDP16K (CLK2, CLK3, A1ADDR, A1DATA, A1EN, B1ADDR, B1DATA, B1EN);
	parameter CFG_ABITS = 9;
	parameter CFG_DBITS = 36;
	parameter CFG_ENABLE_A = 4;

	parameter CLKPOL2 = 1;
	parameter CLKPOL3 = 1;
	parameter [18431:0] INIT = 18432'b0;

	parameter _TECHMAP_BITS_CONNMAP_ = 8;
	parameter [_TECHMAP_BITS_CONNMAP_-1:0] _TECHMAP_CONNMAP_CLK2_ = 0;
	parameter [_TECHMAP_BITS_CONNMAP_-1:0] _TECHMAP_CONNMAP_CLK3_ = 0;

	input CLK2;
	input CLK3;

	input [CFG_ABITS-1:0] A1ADDR;
	input [CFG_DBITS-1:0] A1DATA;
	input [CFG_ENABLE_A-1:0] A1EN;

	input [CFG_ABITS-1:0] B1ADDR;
	output [CFG_DBITS-1:0] B1DATA;
	input B1EN;

	// Address is left justified, in x18 and above lower bits are byte enables
	localparam A_SHIFT =
		(CFG_DBITS == 36) ? 5 :
		(CFG_DBITS == 18) ? 4 :
		(CFG_DBITS == 9) ? 3 :
		(CFG_DBITS == 4) ? 2 :
		(CFG_DBITS == 2) ? 1 :
		0;

	// Different primitives needed for single vs dual clock case
	localparam SINGLE_CLOCK = (_TECHMAP_CONNMAP_CLK2_ == _TECHMAP_CONNMAP_CLK3_);

	localparam WIDTH = $sformatf("X%d", CFG_DBITS);

	wire [13:0] ra, wa;
	wire [35:0] rd, wd;

	assign ra = {B1ADDR, {A_SHIFT{1'b1}}};

	generate
		if (CFG_ENABLE_A > 1)
			assign wa = {A1ADDR, {(A_SHIFT-CFG_ENABLE_A){1'b1}}, A1EN};
		else
			assign wa = {A1ADDR, {A_SHIFT{1'b1}}};
	endgenerate

	assign wd = A1DATA;
	assign B1DATA = rd[CFG_DBITS-1:0];

	wire wck, rck;

	generate
		if (CLKPOL2)
			assign wck = CLK2;
		else
			INV wck_inv_i (.A(CLK2), .Z(wck));
		if (CLKPOL3)
			assign rck = CLK3;
		else
			INV wck_inv_i (.A(CLK3), .Z(rck));
	endgenerate

	wire we = |A1EN;

	localparam INIT_CHUNK_SIZE = (CFG_DBITS <= 4) ? 256 : 288;

	function [319:0] permute_init;
		input [INIT_CHUNK_SIZE-1:0] chunk;
		integer i;
		begin
			if (CFG_DBITS <= 4) begin
				for (i = 0; i < 32; i = i + 1'b1)
					permute_init[i * 10 +: 10] = {2'b00, chunk[i * 8 +: 8]};
			end else begin
				for (i = 0; i < 32; i = i + 1'b1)
					permute_init[i * 10 +: 10] = {1'b0, chunk[i * 9 +: 9]};
			end
		end
	endfunction

	generate
		if (SINGLE_CLOCK) begin
			PDPSC16K #(
				.DATA_WIDTH_W(WIDTH),
				.DATA_WIDTH_R(WIDTH),
				.OUTREG("BYPASSED"),
				.ECC("DISABLED"),
				.GSR("DISABLED"),
`include "brams_init.vh"
			) _TECHMAP_REPLACE_ (
				.CLK(wck), .RST(1'b0),
				.DI(wd), .ADW(wa), .CEW(we), .CSW(3'b111),
				.ADR(ra), .DO(rd), .CER(B1EN), .CSR(3'b111)
			);
		end else begin
			PDP16K #(
				.DATA_WIDTH_W(WIDTH),
				.DATA_WIDTH_R(WIDTH),
				.OUTREG("BYPASSED"),
				.ECC("DISABLED"),
				.GSR("DISABLED"),
`include "brams_init.vh"
			) _TECHMAP_REPLACE_ (
				.CLKW(wck), .CLKR(rck), .RST(1'b0),
				.DI(wd), .ADW(wa), .CEW(we), .CSW(3'b111),
				.ADR(ra), .DO(rd), .CER(B1EN), .CSR(3'b111)
			);
		end
	endgenerate

endmodule
