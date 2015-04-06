module bram1_tb #(
	parameter ABITS = 8, DBITS = 8, TRANSP = 0
);
	reg clk;
	reg [ABITS-1:0] WR_ADDR;
	reg [DBITS-1:0] WR_DATA;
	reg WR_EN;
	reg [ABITS-1:0] RD_ADDR;
	wire [DBITS-1:0] RD_DATA;

	localparam [ABITS-1:0] INIT_ADDR_0 = 1234;
	localparam [ABITS-1:0] INIT_ADDR_1 = 4321;
	localparam [ABITS-1:0] INIT_ADDR_2 = 2**ABITS-1;
	localparam [ABITS-1:0] INIT_ADDR_3 = (2**ABITS-1) / 2;

	localparam [DBITS-1:0] INIT_DATA_0 = 128'h 51e152a7300e309ccb8cd06d34558f49;
	localparam [DBITS-1:0] INIT_DATA_1 = 128'h 07b1fe94a530ddf3027520f9d23ab43e;
	localparam [DBITS-1:0] INIT_DATA_2 = 128'h 3cedc6de43ef3f607af3193658d0eb0b;
	localparam [DBITS-1:0] INIT_DATA_3 = 128'h f6bc5514a8abf1e2810df966bcc13b46;

	bram1 #(
		// .ABITS(ABITS),
		// .DBITS(DBITS),
		// .TRANSP(TRANSP)
	) uut  (
		.clk    (clk    ),
		.WR_ADDR(WR_ADDR),
		.WR_DATA(WR_DATA),
		.WR_EN  (WR_EN  ),
		.RD_ADDR(RD_ADDR),
		.RD_DATA(RD_DATA)
	);

	reg [63:0] xorshift64_state = 64'd88172645463325252 ^ (ABITS << 24) ^ (DBITS << 16) ^ (TRANSP << 8);

	task xorshift64_next;
		begin
		// see page 4 of Marsaglia, George (July 2003). "Xorshift RNGs". Journal of Statistical Software 8 (14).
		xorshift64_state = xorshift64_state ^ (xorshift64_state << 13);
		xorshift64_state = xorshift64_state ^ (xorshift64_state >>  7);
		xorshift64_state = xorshift64_state ^ (xorshift64_state << 17);
		end
	endtask

	reg [ABITS-1:0] randaddr1;
	reg [ABITS-1:0] randaddr2;
	reg [ABITS-1:0] randaddr3;

	function [31:0] getaddr(input [3:0] n);
		begin
			case (n)
				0: getaddr = 0;
				1: getaddr = 2**ABITS-1;
				2: getaddr = 'b101 << (ABITS / 3);
				3: getaddr = 'b101 << (2*ABITS / 3);
				4: getaddr = 'b11011 << (ABITS / 4);
				5: getaddr = 'b11011 << (2*ABITS / 4);
				6: getaddr = 'b11011 << (3*ABITS / 4);
				7: getaddr = randaddr1;
				8: getaddr = randaddr2;
				9: getaddr = randaddr3;
				default: begin
					getaddr = 1 << (2*n-16);
					if (!getaddr) getaddr = xorshift64_state;
				end
			endcase
		end
	endfunction

	reg [DBITS-1:0] memory [0:2**ABITS-1];
	reg [DBITS-1:0] expected_rd, expected_rd_masked;

	event error;
	reg error_ind = 0;

	integer i, j;
	initial begin
		// $dumpfile("testbench.vcd");
		// $dumpvars(0, bram1_tb);

		memory[INIT_ADDR_0] = INIT_DATA_0;
		memory[INIT_ADDR_1] = INIT_DATA_1;
		memory[INIT_ADDR_2] = INIT_DATA_2;
		memory[INIT_ADDR_3] = INIT_DATA_3;

		xorshift64_next;
		xorshift64_next;
		xorshift64_next;
		xorshift64_next;

		randaddr1 = xorshift64_state;
		xorshift64_next;

		randaddr2 = xorshift64_state;
		xorshift64_next;

		randaddr3 = xorshift64_state;
		xorshift64_next;

		clk <= 0;
		for (i = 0; i < 512; i = i+1) begin
			if (i == 0) begin
				WR_EN <= 0;
				RD_ADDR <= INIT_ADDR_0;
			end else
			if (i == 1) begin
				WR_EN <= 0;
				RD_ADDR <= INIT_ADDR_1;
			end else
			if (i == 2) begin
				WR_EN <= 0;
				RD_ADDR <= INIT_ADDR_2;
			end else
			if (i == 3) begin
				WR_EN <= 0;
				RD_ADDR <= INIT_ADDR_3;
			end else begin
				if (DBITS > 64)
					WR_DATA <= (xorshift64_state << (DBITS-64)) ^ xorshift64_state;
				else
					WR_DATA <= xorshift64_state;
				xorshift64_next;
				WR_ADDR <= getaddr(i < 256 ? i[7:4] : xorshift64_state[63:60]);
				xorshift64_next;
				RD_ADDR <= getaddr(i < 256 ? i[3:0] : xorshift64_state[59:56]);
				WR_EN <= xorshift64_state[55];
				xorshift64_next;
			end

			#1; clk <= 1;
			#1; clk <= 0;

			if (TRANSP) begin
				if (WR_EN) memory[WR_ADDR] = WR_DATA;
				expected_rd = memory[RD_ADDR];
			end else begin
				expected_rd = memory[RD_ADDR];
				if (WR_EN) memory[WR_ADDR] = WR_DATA;
			end

			for (j = 0; j < DBITS; j = j+1)
				expected_rd_masked[j] = expected_rd[j] !== 1'bx ? expected_rd[j] : RD_DATA[j];

			$display("#OUT# %3d | WA=%x WD=%x WE=%x | RA=%x RD=%x (%x) | %s", i, WR_ADDR, WR_DATA, WR_EN, RD_ADDR, RD_DATA, expected_rd, expected_rd_masked === RD_DATA ? "ok" : "ERROR");
			if (expected_rd_masked !== RD_DATA) begin -> error; error_ind = ~error_ind; end
		end
	end
endmodule
