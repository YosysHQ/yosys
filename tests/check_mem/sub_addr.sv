module memtest05(clk, addr, wdata, rdata, wen);

input clk;
input [1:0] addr;
input [7:0] wdata;
output reg [7:0] rdata;
input [3:0] wen;

reg [7:0] mem [0:3] = {8'h01, 8'h23, 8'h45, 8'h67};

integer i;
always @(posedge clk) begin
	for (i = 0; i < 4; i = i+1)
		if (wen[i]) mem[addr][i*2 +: 2] <= wdata[i*2 +: 2];
	rdata <= mem[addr];
end

always @(posedge clk) begin
	// not sure how to verify this one without SBY
	// or alternatively, how to replicate the problematic sub addressing without the read&write
	assume (wen == 0);
	assert (mem[0][7:4] == 4'h0);
	assert (mem[0][3:0] == 4'h1);
	assert (mem[1][7:4] == 4'h2);
	assert (mem[1][3:0] == 4'h3);
	assert (mem[2][7:4] == 4'h4);
	assert (mem[2][3:0] == 4'h5);
	assert (mem[3][7:4] == 4'h6);
	assert (mem[3][3:0] == 4'h7);
end

endmodule
