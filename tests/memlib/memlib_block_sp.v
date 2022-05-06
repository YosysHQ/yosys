module RAM_BLOCK_SP(
	input PORT_A_CLK,
	input PORT_A_CLK_EN,
	input PORT_A_RD_EN,
	input PORT_A_RD_ARST,
	input PORT_A_RD_SRST,
	input [1:0] PORT_A_WR_EN,
	input [3:0] PORT_A_ADDR,
	output reg [15:0] PORT_A_RD_DATA,
	input [15:0] PORT_A_WR_DATA
);

parameter OPTION_RDWR = "UNDEFINED";
parameter OPTION_RDINIT = "UNDEFINED";
parameter OPTION_RDARST = "UNDEFINED";
parameter OPTION_RDSRST = "UNDEFINED";
parameter OPTION_SRST_GATE = 0;
parameter PORT_A_RD_INIT_VALUE = 16'hxxxx;
parameter PORT_A_RD_ARST_VALUE = 16'hxxxx;
parameter PORT_A_RD_SRST_VALUE = 16'hxxxx;

reg [15:0] mem [0:15];

initial
	if (OPTION_RDINIT == "ZERO")
		PORT_A_RD_DATA = 0;
	else if (OPTION_RDINIT == "ANY")
		PORT_A_RD_DATA = PORT_A_RD_INIT_VALUE;

localparam ARST_VALUE = 
	(OPTION_RDARST == "ZERO") ? 16'h0000 :
	(OPTION_RDARST == "INIT") ? PORT_A_RD_INIT_VALUE :
	(OPTION_RDARST == "ANY") ? PORT_A_RD_ARST_VALUE :
	16'hxxxx;

localparam SRST_VALUE = 
	(OPTION_RDSRST == "ZERO") ? 16'h0000 :
	(OPTION_RDSRST == "INIT") ? PORT_A_RD_INIT_VALUE :
	(OPTION_RDSRST == "ANY") ? PORT_A_RD_SRST_VALUE :
	16'hxxxx;

pullup (PORT_A_CLK_EN);
pullup (PORT_A_RD_EN);
pulldown (PORT_A_RD_ARST);
pulldown (PORT_A_RD_SRST);

always @(posedge PORT_A_CLK) begin
	if (PORT_A_CLK_EN) begin
		if (PORT_A_WR_EN[0])
			mem[PORT_A_ADDR][7:0] <= PORT_A_WR_DATA[7:0];
		if (PORT_A_WR_EN[1])
			mem[PORT_A_ADDR][15:8] <= PORT_A_WR_DATA[15:8];
		if (PORT_A_RD_EN && (!PORT_A_WR_EN || OPTION_RDWR != "NO_CHANGE")) begin
			PORT_A_RD_DATA <= mem[PORT_A_ADDR];
			if (PORT_A_WR_EN && OPTION_RDWR == "NEW_ONLY")
				PORT_A_RD_DATA <= 16'hx;
			if (PORT_A_WR_EN[0])
				case (OPTION_RDWR)
				"NEW": PORT_A_RD_DATA[7:0] <= PORT_A_WR_DATA[7:0];
				"NEW_ONLY": PORT_A_RD_DATA[7:0] <= PORT_A_WR_DATA[7:0];
				"UNDEFINED": PORT_A_RD_DATA[7:0] <= 8'hx;
				endcase
			if (PORT_A_WR_EN[1])
				case (OPTION_RDWR)
				"NEW": PORT_A_RD_DATA[15:8] <= PORT_A_WR_DATA[15:8];
				"NEW_ONLY": PORT_A_RD_DATA[15:8] <= PORT_A_WR_DATA[15:8];
				"UNDEFINED": PORT_A_RD_DATA[15:8] <= 8'hx;
				endcase
		end
	end
	if (PORT_A_RD_SRST && (!OPTION_SRST_GATE || (OPTION_SRST_GATE == 2 && PORT_A_RD_EN) || (OPTION_SRST_GATE == 1 && PORT_A_CLK_EN)))
		PORT_A_RD_DATA <= SRST_VALUE;
end

always @(PORT_A_RD_ARST)
	if (PORT_A_RD_ARST)
		force PORT_A_RD_DATA = ARST_VALUE;
	else
		release PORT_A_RD_DATA;

endmodule
