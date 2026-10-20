module tb;

reg clk, rst;
wire [7:0] out;
wire [4:0] counter;

uut uut (clk, rst, out, counter);

initial begin
	#5 clk <= 0;
	repeat (100) #5 clk <= ~clk;
	#5 $finish;
end

initial begin
	rst <= 1;
	repeat (2) @(posedge clk);
	rst <= 0;
end

always @(posedge clk)
	$display("%d %d %d", rst, out, counter);

initial begin
	$dumpfile("mem_simple_4x1_tb.vcd");
	$dumpvars(0, uut);
end

endmodule
