module memtest05(clk, addr, wdata, rdata, wen);

input clk;
input [1:0] addr;
input [7:0] wdata;
output reg [7:0] rdata;
input [3:0] wen;

reg [7:0] mem [0:3];

integer i;
always @(posedge clk) begin
	for (i = 0; i < 4; i = i+1)
		if (wen[i]) mem[addr][i*2 +: 2] <= wdata[i*2 +: 2];
	rdata <= mem[addr];
end

endmodule
