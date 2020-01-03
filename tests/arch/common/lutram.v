module lutram_1w1r
#(parameter D_WIDTH=8, A_WIDTH=6)
(
	input [D_WIDTH-1:0] data_a,
	input [A_WIDTH:1] addr_a,
	input we_a, clk,
	output reg [D_WIDTH-1:0] q_a
);
	// Declare the RAM variable
	reg [D_WIDTH-1:0] ram[(2**A_WIDTH)-1:0];

	// Port A
	always @ (posedge clk)
	begin
		if (we_a)
			ram[addr_a] <= data_a;
		q_a <= ram[addr_a];
	end
endmodule


module lutram_1w3r
#(parameter D_WIDTH=8, A_WIDTH=5)
(
	input [D_WIDTH-1:0] data_a, data_b, data_c,
	input [A_WIDTH:1] addr_a, addr_b, addr_c,
	input we_a, clk,
	output reg [D_WIDTH-1:0] q_a, q_b, q_c
);
	// Declare the RAM variable
	reg [D_WIDTH-1:0] ram[(2**A_WIDTH)-1:0];

	// Port A
	always @ (posedge clk)
	begin
		if (we_a)
			ram[addr_a] <= data_a;
		q_a <= ram[addr_a];
		q_b <= ram[addr_b];
		q_c <= ram[addr_c];
	end
endmodule
