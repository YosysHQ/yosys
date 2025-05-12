module priority_memory (
	clk, wren_a, rden_a, addr_a, wdata_a, rdata_a,
	wren_b, rden_b, addr_b, wdata_b, rdata_b
	);

	parameter ABITS = 12;
	parameter WIDTH = 72;

	input clk;
	input wren_a, rden_a, wren_b, rden_b;
	input [ABITS-1:0] addr_a, addr_b;
	input [WIDTH-1:0] wdata_a, wdata_b;
	output reg [WIDTH-1:0] rdata_a, rdata_b;

	`ifdef USE_HUGE
	(* ram_style = "huge" *)
	`endif
	reg [WIDTH-1:0] mem [0:2**ABITS-1];

	integer i;
	initial begin
		rdata_a <= 'h0;
		rdata_b <= 'h0;
	end

	`ifndef FLIP_PORTS
	always @(posedge clk) begin
		// A port
		if (wren_a)
			mem[addr_a] <= wdata_a;
		else if (rden_a)
			rdata_a <= mem[addr_a];

		// B port
		if (wren_b)
			mem[addr_b] <= wdata_b;
		else if (rden_b)
			if (wren_a && addr_a == addr_b)
				rdata_b <= wdata_a;
			else
				rdata_b <= mem[addr_b];
	end
	`else // FLIP PORTS
	always @(posedge clk) begin
		// A port
		if (wren_b)
			mem[addr_b] <= wdata_b;
		else if (rden_b)
			rdata_b <= mem[addr_b];

		// B port
		if (wren_a)
			mem[addr_a] <= wdata_a;
		else if (rden_a)
			if (wren_b && addr_a == addr_b)
				rdata_a <= wdata_b;
			else
				rdata_a <= mem[addr_a];
	end
	`endif
endmodule

module sp_write_first (clk, wren_a, rden_a, addr_a, wdata_a, rdata_a);

	parameter ABITS = 12;
	parameter WIDTH = 72;

	input clk;
	input wren_a, rden_a;
	input [ABITS-1:0] addr_a;
	input [WIDTH-1:0] wdata_a;
	output reg [WIDTH-1:0] rdata_a;

	(* ram_style = "huge" *)
	reg [WIDTH-1:0] mem [0:2**ABITS-1];

	integer i;
	initial begin
		rdata_a <= 'h0;
	end

	always @(posedge clk) begin
		// A port
		if (wren_a)
			mem[addr_a] <= wdata_a;
		if (rden_a)
			if (wren_a)
				rdata_a <= wdata_a;
			else
				rdata_a <= mem[addr_a];
	end
endmodule

module sp_read_first (clk, wren_a, rden_a, addr_a, wdata_a, rdata_a);

	parameter ABITS = 12;
	parameter WIDTH = 72;

	input clk;
	input wren_a, rden_a;
	input [ABITS-1:0] addr_a;
	input [WIDTH-1:0] wdata_a;
	output reg [WIDTH-1:0] rdata_a;

	(* ram_style = "huge" *)
	reg [WIDTH-1:0] mem [0:2**ABITS-1];

	integer i;
	initial begin
		rdata_a <= 'h0;
	end

	always @(posedge clk) begin
		// A port
		if (wren_a)
			mem[addr_a] <= wdata_a;
		if (rden_a)
			rdata_a <= mem[addr_a];
	end
endmodule

module sp_read_or_write (clk, wren_a, rden_a, addr_a, wdata_a, rdata_a);

	parameter ABITS = 11;
	parameter WIDTH = 144;

	input clk;
	input wren_a, rden_a;
	input [ABITS-1:0] addr_a;
	input [WIDTH-1:0] wdata_a;
	output reg [WIDTH-1:0] rdata_a;

	(* ram_style = "huge" *)
	reg [WIDTH-1:0] mem [0:2**ABITS-1];

	integer i;
	initial begin
		rdata_a <= 'h0;
	end

	always @(posedge clk) begin
		if (wren_a)
			mem[addr_a] <= wdata_a;
		else if (rden_a)
			rdata_a <= mem[addr_a];
	end

endmodule
