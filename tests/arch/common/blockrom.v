`default_nettype none
module sync_rom #(parameter DATA_WIDTH=8, ADDRESS_WIDTH=10)
	 (input  wire                      clk,
		input  wire  [ADDRESS_WIDTH-1:0] address_in,
		output wire  [DATA_WIDTH-1:0]    data_out);

	localparam WORD  = (DATA_WIDTH-1);
	localparam DEPTH = (2**ADDRESS_WIDTH-1);

	reg [WORD:0] data_out_r;
	reg [WORD:0] memory [0:DEPTH];

	integer i,j = 16'hACE1;
	initial
		for (i = 0; i <= DEPTH; i++) begin
			// In case this ROM will be implemented in fabric: fill the memory with some data
			// uncorrelated with the address, or Yosys might see through the ruse and e.g. not
			// emit any LUTs at all for `memory[i] = i;`, just a latch.
			memory[i] = j;
			j = j ^ (j >> 7);
			j = j ^ (j << 9);
			j = j ^ (j >> 13);
		end

	always @(posedge clk) begin
		data_out_r <= memory[address_in];
	end

	assign data_out = data_out_r;

endmodule // sync_rom
