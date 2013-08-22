`timescale  1 ns / 1 ps

module testbench;

reg clk, en, rst;
wire [3:0] count;

counter uut_counter(
	.clk(clk),
	.count(count),
	.en(en),
	.rst(rst)
);

initial begin
	clk <= 0;
	forever begin
		#50;
		clk <= ~clk;
	end
end

initial begin
	@(posedge clk);
	forever begin
		@(posedge clk);
		$display("%d", count);
	end
end

initial begin
	rst <= 1; en <= 0; @(posedge clk);
	rst <= 1; en <= 0; @(posedge clk);
	rst <= 0; en <= 0; @(posedge clk);
	rst <= 0; en <= 1; @(posedge clk);
	rst <= 0; en <= 1; @(posedge clk);
	rst <= 0; en <= 1; @(posedge clk);
	rst <= 0; en <= 0; @(posedge clk);
	rst <= 0; en <= 1; @(posedge clk);
	rst <= 0; en <= 1; @(posedge clk);
	rst <= 0; en <= 1; @(posedge clk);
	rst <= 1; en <= 1; @(posedge clk);
	rst <= 0; en <= 0; @(posedge clk);
	rst <= 0; en <= 1; @(posedge clk);
	rst <= 0; en <= 1; @(posedge clk);
	rst <= 0; en <= 0; @(posedge clk);
	rst <= 0; en <= 1; @(posedge clk);
	rst <= 0; en <= 1; @(posedge clk);
	rst <= 0; en <= 0; @(posedge clk);
	rst <= 1; en <= 0; @(posedge clk);
	rst <= 0; en <= 1; @(posedge clk);
	rst <= 0; en <= 0; @(posedge clk);
	rst <= 0; en <= 1; @(posedge clk);
	rst <= 0; en <= 1; @(posedge clk);
	rst <= 0; en <= 0; @(posedge clk);
	rst <= 0; en <= 1; @(posedge clk);
	rst <= 0; en <= 0; @(posedge clk);
	$finish;
end

endmodule
