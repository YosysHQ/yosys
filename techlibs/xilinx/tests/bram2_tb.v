`timescale 1 ns / 1 ps

module testbench;
	reg         rd_clk;
	reg  [ 7:0] rd_addr;
	wire [17:0] rd_data;

	wire        wr_clk    = 0;
	wire        wr_enable = 0;
	wire [ 7:0] wr_addr   = 0;
	wire [17:0] wr_data   = 0;

	function [17:0] hash(input [7:0] k);
		reg [31:0] x;
		begin
			x = {k, ~k, k, ~k};
			x = x ^ (x << 13);
			x = x ^ (x >> 17);
			x = x ^ (x << 5);
			hash = x;
		end
	endfunction

	myram uut (
		.rd_clk   (rd_clk   ),
		.rd_addr  (rd_addr  ),
		.rd_data  (rd_data  ),
		.wr_clk   (wr_clk   ),
		.wr_enable(wr_enable),
		.wr_addr  (wr_addr  ),
		.wr_data  (wr_data  )
	);

	initial begin
		rd_clk = 0;
		#1000;
		forever #10 rd_clk <= ~rd_clk;
	end

	integer i;
	initial begin
		rd_addr <= 0;
		@(posedge rd_clk);
		for (i = 0; i < 256; i=i+1) begin
			rd_addr <= rd_addr + 1;
			@(posedge rd_clk);
			// $display("%3d %3d", i, rd_data);
			if (hash(i) !== rd_data) begin
				$display("[%1t] ERROR: addr=%3d, data_mem=%18b, data_ref=%18b", $time, i, rd_data, hash(i));
				$stop;
			end
		end
		$display("[%1t] Passed bram2 test.", $time);
		$finish;
	end
endmodule
