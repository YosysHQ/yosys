module test001(output [63:0] y);
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

	genvar i;
	generate
		for (i = 0; i < 64; i = i+1) begin
			localparam tmp = mylog2(i);
			assign y[i] = tmp;
		end
	endgenerate
endmodule
