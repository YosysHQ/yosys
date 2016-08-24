// Whatever the initial content of this memory is at reset, it will never change
// see demo3.smtc for assumptions and assertions

module demo3(input clk, rst, input [15:0] addr, output reg [31:0] data);
	reg [31:0] mem [0:2**16-1];
	reg [15:0] addr_q;

	always @(posedge clk) begin
		if (rst) begin
			data <= mem[0] ^ 123456789;
			addr_q <= 0;
		end else begin
			mem[addr_q] <= data ^ 123456789;
			data <= mem[addr] ^ 123456789;
			addr_q <= addr;
		end
	end
endmodule
