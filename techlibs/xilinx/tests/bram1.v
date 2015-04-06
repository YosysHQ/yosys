module bram1 #(
	parameter ABITS = 8, DBITS = 8, TRANSP = 0
) (
	input clk,

	input [ABITS-1:0] WR_ADDR,
	input [DBITS-1:0] WR_DATA,
	input WR_EN,

	input [ABITS-1:0] RD_ADDR,
	output [DBITS-1:0] RD_DATA
);
	localparam [ABITS-1:0] INIT_ADDR_0 = 1234;
	localparam [ABITS-1:0] INIT_ADDR_1 = 4321;
	localparam [ABITS-1:0] INIT_ADDR_2 = 2**ABITS-1;
	localparam [ABITS-1:0] INIT_ADDR_3 = (2**ABITS-1) / 2;

	localparam [DBITS-1:0] INIT_DATA_0 = 128'h 51e152a7300e309ccb8cd06d34558f49;
	localparam [DBITS-1:0] INIT_DATA_1 = 128'h 07b1fe94a530ddf3027520f9d23ab43e;
	localparam [DBITS-1:0] INIT_DATA_2 = 128'h 3cedc6de43ef3f607af3193658d0eb0b;
	localparam [DBITS-1:0] INIT_DATA_3 = 128'h f6bc5514a8abf1e2810df966bcc13b46;

	reg [DBITS-1:0] memory [0:2**ABITS-1];
	reg [ABITS-1:0] RD_ADDR_BUF;
	reg [DBITS-1:0] RD_DATA_BUF;

	initial begin
		memory[INIT_ADDR_0] <= INIT_DATA_0;
		memory[INIT_ADDR_1] <= INIT_DATA_1;
		memory[INIT_ADDR_2] <= INIT_DATA_2;
		memory[INIT_ADDR_3] <= INIT_DATA_3;
	end

	always @(posedge clk) begin
		if (WR_EN) memory[WR_ADDR] <= WR_DATA;
		RD_ADDR_BUF <= RD_ADDR;
		RD_DATA_BUF <= memory[RD_ADDR];
	end

	assign RD_DATA = TRANSP ? memory[RD_ADDR_BUF] : RD_DATA_BUF;
endmodule
