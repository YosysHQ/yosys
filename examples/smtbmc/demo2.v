// Nothing to prove in this demo.
// Just an example for memories, vcd dumps and vlog testbench dumps.

`ifdef FORMAL
`define assume(_expr_) assume(_expr_)
`else
`define assume(_expr_)
`endif

module demo2(input clk, input [4:0] addr, output reg [31:0] data);
	reg [31:0] mem [0:31];
	always @(posedge clk)
		data <= mem[addr];

	reg [31:0] used_addr = 0;
	reg [31:0] used_dbits = 0;
	reg initstate = 1;

	always @(posedge clk) begin
		initstate <= 0;
		`assume(!used_addr[addr]);
		used_addr[addr] <= 1;
		if (!initstate) begin
			`assume(data != 0);
			`assume((used_dbits & data) == 0);
			used_dbits <= used_dbits | data;
		end
	end
endmodule
