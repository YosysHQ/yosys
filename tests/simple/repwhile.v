module repwhile_test001(input [5:0] a, output [7:0] y, output [31:0] x);

	function [7:0] mylog2;
		input [31:0] value;
		begin
			mylog2 = 0;
			while (value > 0) begin
				value = value >> 1;
				mylog2 = mylog2 + 1;
			end
		end
	endfunction

	function [31:0] myexp2;
		input [7:0] value;
		begin
			myexp2 = 1;
			repeat (value)
				myexp2 = myexp2 << 1;
		end
	endfunction

	reg [7:0] y_table [63:0];
	reg [31:0] x_table [63:0];

	integer i;
	initial begin
		for (i = 0; i < 64; i = i+1) begin
			y_table[i] <= mylog2(i);
			x_table[i] <= myexp2(i);
		end
	end

	assign y = y_table[a];
	assign x = x_table[a];
endmodule
