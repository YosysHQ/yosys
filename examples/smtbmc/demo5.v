// Demo for $anyconst

module demo5 (input clk);
	wire [7:0] step_size = $anyconst;
	reg [7:0] state = 0, count = 0;
	reg [31:0] hash = 0;

	always @(posedge clk) begin
		count <= count + 1;
		hash <= ((hash << 5) + hash) ^ state;
		state <= state + step_size;
	end

	always @* begin
		if (count == 42)
			assert(hash == 32'h A18FAC0A);
	end
endmodule
