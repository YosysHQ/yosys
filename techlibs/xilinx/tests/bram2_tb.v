`timescale 1 ns / 1 ps

module testbench;
	reg         rd_clk;
	reg  [ 7:0] rd_addr;
	wire [15:0] rd_data;

	wire        wr_clk    = 0;
	wire        wr_enable = 0;
	wire [ 7:0] wr_addr   = 0;
	wire [15:0] wr_data   = 0;

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
			if (i != rd_data) begin
				$display("[%1t] ERROR: addr=%3d, data=%3d", $time, i, rd_data);
				$stop;
			end
		end
		$display("[%1t] Passed bram2 test.", $time);
		$finish;
	end
endmodule
