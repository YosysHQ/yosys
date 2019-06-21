module uut_arrays02(clock, we, addr, wr_data, rd_data);

input clock, we;
input [3:0] addr, wr_data;
output [3:0] rd_data;
reg [3:0] rd_data;

reg [3:0] memory [16];

always @(posedge clock) begin
	if (we)
		memory[addr] <= wr_data;
	rd_data <= memory[addr];
end

endmodule
