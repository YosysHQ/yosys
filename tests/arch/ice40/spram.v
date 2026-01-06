module top (clk, write_enable, read_enable, write_data, addr, read_data);
parameter DATA_WIDTH = 8;
parameter ADDR_WIDTH = 8;
parameter SKIP_RDEN = 1;

input clk;
input write_enable, read_enable;
input [DATA_WIDTH - 1 : 0] write_data;
input [ADDR_WIDTH - 1 : 0] addr; 
output [DATA_WIDTH - 1 : 0] read_data;

(* ram_style = "huge" *)
reg [DATA_WIDTH - 1 : 0] mem [2**ADDR_WIDTH - 1 : 0];

always @(posedge clk) begin
	if (write_enable)
		mem[addr] <= write_data;
	else if (SKIP_RDEN || read_enable)
		read_data <= mem[addr];
end

endmodule
