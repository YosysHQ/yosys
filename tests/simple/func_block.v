`default_nettype none

module top(inp, out1, out2, out3);
	input wire [31:0] inp;

	function automatic [31:0] func1;
		input [31:0] inp;
		reg [31:0] idx;
		for (idx = 0; idx < 32; idx = idx + 1) begin : blk
			func1[idx] = (idx & 1'b1) ^ inp[idx];
		end
	endfunction

	function automatic [31:0] func2;
		input [31:0] inp;
		reg [31:0] idx;
		for (idx = 0; idx < 32; idx = idx + 1) begin : blk
			func2[idx] = (idx & 1'b1) ^ inp[idx];
		end
	endfunction

	function automatic [31:0] func3;
		localparam A = 32 - 1;
		parameter B = 1 - 0;
		input [31:0] inp;
		func3[A:B] = inp[A:B];
	endfunction

	output wire [31:0] out1, out2, out3;
	assign out1 = func1(inp);
	assign out2 = func2(inp);
	assign out3 = func3(inp);
endmodule
