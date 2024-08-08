module gold(
	input wire clk,
	output reg resetn,
	output wire trap,
	output wire mem_valid,
	output wire mem_instr,
	output wire mem_ready,
	output wire [31:0] mem_addr,
	output wire [31:0] mem_wdata,
	output wire [31:0] mem_wstrb,
	output wire [31:0] mem_rdata,
);

	initial resetn = 1'b0;
	always @(posedge clk) resetn <= 1'b1;

	reg [31:0] rom[0:15];

	initial begin
		rom[0]  = 32'h00200093;
		rom[1]  = 32'h00200113;
		rom[2]  = 32'h00111863;
		rom[3]  = 32'h00102023;
		rom[4]  = 32'h00108093;
		rom[5]  = 32'hfe0008e3;
		rom[6]  = 32'h00008193;
		rom[7]  = 32'h402181b3;
		rom[8]  = 32'hfe304ee3;
		rom[9]  = 32'hfe0186e3;
		rom[10] = 32'h00110113;
		rom[11] = 32'hfc000ee3;
	end

	assign mem_ready = 1'b1;
	assign mem_rdata = rom[mem_addr[5:2]];

	wire pcpi_wr = 1'b0;
	wire [31:0] pcpi_rd = 32'b0;
	wire pcpi_wait = 1'b0;
	wire pcpi_ready = 1'b0;

	wire [31:0] irq = 32'b0;

	picorv32 picorv32_i(
		.clk(clk),
		.resetn(resetn),
		.trap(trap),
		.mem_valid(mem_valid),
		.mem_instr(mem_instr),
		.mem_ready(mem_ready),
		.mem_addr(mem_addr),
		.mem_wdata(mem_wdata),
		.mem_wstrb(mem_wstrb),
		.mem_rdata(mem_rdata),
		.pcpi_wr(pcpi_wr),
		.pcpi_rd(pcpi_rd),
		.pcpi_wait(pcpi_wait),
		.pcpi_ready(pcpi_ready),
		.irq(irq)
	);

endmodule
