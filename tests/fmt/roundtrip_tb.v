module tb;
	reg clk = 1'b0;
	reg [31:0] data;

	m dut(.clk(clk), .data(data));

	initial begin
		data = 32'haa;
		#10; clk = 1; #10; clk = 0;
		data = 32'haaaa;
		#10; clk = 1; #10; clk = 0;
	end
endmodule
