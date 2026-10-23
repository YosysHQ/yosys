module real_func(input [7:0] i, output [7:0] a);
	function [7:0] doubled;
		input real k;
		real r;
		begin
			r = k * 2.0;
			doubled = r;
		end
	endfunction
	localparam [7:0] A = doubled(1.3);
	assign a = i ^ A;
endmodule
