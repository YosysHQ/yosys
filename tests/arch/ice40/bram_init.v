// Test design for SB_RAM40_4K initialization data generation.
// Four widths, all would fit into one RAM40_4K (4096 bits)
// with random init data taken from bram_init_<width>.hex.
// random init data is from author's /dev/random.

module ram16 (clk, we, addr, wdata, rdata);
input clk, we;
input [7:0] addr;
input [15:0] wdata;
output reg [15:0] rdata;

reg [15:0] mem [0:255];
initial $readmemh("bram_init_16.hex", mem);

always @(posedge clk) begin
	if (we)
		mem[addr] <= wdata;
	rdata <= mem[addr];
end

endmodule

module ram8 (clk, we, addr, wdata, rdata);
input clk, we;
input [8:0] addr;
input [7:0] wdata;
output reg [7:0] rdata;

reg [7:0] mem [0:511];
initial $readmemh("bram_init_8.hex", mem);

always @(posedge clk) begin
	if (we)
		mem[addr] <= wdata;
	rdata <= mem[addr];
end

endmodule

module ram4 (clk, we, addr, wdata, rdata);
input clk, we;
input [9:0] addr;
input [3:0] wdata;
output reg [3:0] rdata;

reg [3:0] mem [0:1023];
initial $readmemh("bram_init_4.hex", mem);

always @(posedge clk) begin
	if (we)
		mem[addr] <= wdata;
	rdata <= mem[addr];
end

endmodule

module ram2 (clk, we, addr, wdata, rdata);
input clk, we;
input [10:0] addr;
input [1:0] wdata;
output reg [1:0] rdata;

reg [1:0] mem [0:2047];
initial $readmemh("bram_init_2.hex", mem);

always @(posedge clk) begin
	if (we)
		mem[addr] <= wdata;
	rdata <= mem[addr];
end

endmodule
