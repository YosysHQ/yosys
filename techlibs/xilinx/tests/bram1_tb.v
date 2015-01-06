module bram1_tb #(
	parameter ABITS = 8, DBITS = 8, TRANSP = 0
);
	reg clk;
	reg [ABITS-1:0] WR_ADDR;
	reg [DBITS-1:0] WR_DATA;
	reg WR_EN;
	reg [ABITS-1:0] RD_ADDR;
	wire [DBITS-1:0] RD_DATA;

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
				7: getaddr = 123456789;
				default: getaddr = 1 << (2*n-16);
			endcase
		end
	endfunction

	reg [DBITS-1:0] memory [0:2**ABITS-1];
	reg [DBITS-1:0] expected_rd;

	event error;
	reg error_ind = 0;

	integer i, j;
	initial begin
		// $dumpfile("testbench.vcd");
		// $dumpvars(0, bram1_tb);
		clk <= 0;
		for (i = 0; i < 256; i = i+1) begin
			WR_DATA <= i;
			WR_ADDR <= getaddr(i[7:4]);
			RD_ADDR <= getaddr(i[3:0]);
			WR_EN <= ^i;

			#1; clk <= 1;
			#1; clk <= 0;

			if (TRANSP) begin
				if (WR_EN) memory[WR_ADDR] = WR_DATA;
				expected_rd = memory[RD_ADDR];
			end else begin
				expected_rd = memory[RD_ADDR];
				if (WR_EN) memory[WR_ADDR] = WR_DATA;
			end

			for (j = 0; j < DBITS; j = j+1) begin
				if (expected_rd[j] === 1'bx)
					expected_rd[j] = RD_DATA[j];
			end

			$display("#OUT# | WA=%x WD=%x WE=%x | RA=%x RD=%x | %s", WR_ADDR, WR_DATA, WR_EN, RD_ADDR, RD_DATA, expected_rd === RD_DATA ? "ok" : "ERROR");
			if (expected_rd !== RD_DATA) begin -> error; error_ind = ~error_ind; end
		end
	end
endmodule
