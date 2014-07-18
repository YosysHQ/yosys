// expect-wr-ports 1
// expect-rd-ports 1

module generic_sram_byte_en #(
	parameter DATA_WIDTH    = 32,
	parameter ADDRESS_WIDTH = 4
) (
	input                           i_clk,
	input      [DATA_WIDTH-1:0]     i_write_data,
	input                           i_write_enable,
	input      [ADDRESS_WIDTH-1:0]  i_address,
	input      [DATA_WIDTH/8-1:0]   i_byte_enable,
	output reg [DATA_WIDTH-1:0]     o_read_data
);

reg [DATA_WIDTH-1:0] mem [0:2**ADDRESS_WIDTH-1];
integer i;

always @(posedge i_clk) begin
	for (i=0;i<DATA_WIDTH/8;i=i+1)
		if (i_write_enable && i_byte_enable[i])
			mem[i_address][i*8 +: 8] <= i_write_data[i*8 +: 8];
	o_read_data <= mem[i_address];
end

endmodule
