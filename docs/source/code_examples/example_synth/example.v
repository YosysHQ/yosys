module example (
	input clk,
	input rst,
	input inc,
	input [7:0] a,
	input [7:0] b,
	output [15:0] c
);

wire [1:0] state;
wire [7:0] addr;

control ctrl (
	.clk(clk),
	.rst(rst),
	.inc(inc),
	.addr_o(addr),
	.state_o(state)
);

data dat (
	.clk(clk),
	.addr_i(addr),
	.state_i(state),
	.a(a),
	.b(b),
	.c(c)
);

endmodule

module control (
	input clk,
	input rst,
	input inc,
	output [7:0] addr_o,
	output [1:0] state_o
);

reg [1:0] state;
reg [7:0] addr;

always @(posedge clk) begin
	if (rst) begin
		state <= 2'b00;
		addr <= 0;
	end else begin
		if (inc) state <= state + 1'b1;
		addr <= addr + 1'b1;
	end
end

endmodule //control

module data (
	input clk,
	input [7:0] addr_i,
	input [1:0] state_i,
	input [7:0] a,
	input [7:0] b,
	output reg [15:0] c
);

reg [15:0] mem[255:0];

always @(posedge clk) begin
	case (state_i)
		2'b00: mem[addr_i] <= a*b;
		2'b01: mem[addr_i] <= a+b;
		2'b10: mem[addr_i] <= a-b;
		2'b11: mem[addr_i] <= addr_i;
	endcase
	c <= mem[addr_i];
end

endmodule //data
