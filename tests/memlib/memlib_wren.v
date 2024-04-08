module RAM_WREN #(
	parameter ABITS=4,
	parameter WIDTH=8,
	parameter PORT_A_WR_EN_WIDTH=1,
	parameter PORT_A_WR_BE_WIDTH=0,
	parameter OPTION_BYTESIZE=WIDTH,
	parameter WB=OPTION_BYTESIZE
)(
	input PORT_A_CLK,
	input [ABITS-1:0] PORT_A_ADDR,
	input [WIDTH-1:0] PORT_A_WR_DATA,
	output reg [WIDTH-1:0] PORT_A_RD_DATA,
	input [PORT_A_WR_EN_WIDTH-1:0] PORT_A_WR_EN,
	input [PORT_A_WR_BE_WIDTH-1:0] PORT_A_WR_BE
);

reg [WIDTH-1:0] mem [0:2**ABITS-1];

integer i;
always @(posedge PORT_A_CLK) begin
	for (i=0; i<PORT_A_WR_EN_WIDTH; i=i+1) // use PORT_A_WR_EN
		if (!PORT_A_WR_BE_WIDTH && PORT_A_WR_EN[i])
			mem[PORT_A_ADDR][i*WB+:WB] <= PORT_A_WR_DATA[i*WB+:WB];
	for (i=0; i<PORT_A_WR_BE_WIDTH; i=i+1) // use PORT_A_WR_BE
		if (PORT_A_WR_EN[0] && PORT_A_WR_BE[i])
			mem[PORT_A_ADDR][i*WB+:WB] <= PORT_A_WR_DATA[i*WB+:WB];
end

always @(posedge PORT_A_CLK)
	if (!PORT_A_WR_EN[0])
		PORT_A_RD_DATA <= mem[PORT_A_ADDR];

endmodule
