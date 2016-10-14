// Demo for memory initialization

module demo7;
	wire [2:0] addr = $anyseq;
	reg [15:0] memory [0:7];

	initial begin
		memory[0] = 1331;
		memory[1] = 1331 + 1;
		memory[2] = 1331 + 2;
		memory[3] = 1331 + 4;
		memory[4] = 1331 + 8;
		memory[5] = 1331 + 16;
		memory[6] = 1331 + 32;
		memory[7] = 1331 + 64;
	end

	assert property (1000 < memory[addr] && memory[addr] < 2000);
endmodule
