module top
(
	input [7:0] data_a,
	input [6:1] addr_a,
	input we_a, clk,
	output reg [7:0] q_a
);
	// Declare the RAM variable
	reg [7:0] ram[63:0];

	// Port A
	always @ (posedge clk)
	begin
		if (we_a)
		begin
			ram[addr_a] <= data_a;
			q_a <= data_a;
		end
			q_a <= ram[addr_a];
	end

endmodule
