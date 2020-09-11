module top(out);
	function integer operation;
		input integer num;
		localparam incr = 1;
		localparam mult = 1;
		begin
			operation = 0;
			begin : op_i
				integer i;
				for (i = 0; i * mult < 2; i = i + incr)
				begin : op_j
					integer j;
					localparam other_mult = 2;
					for (j = i; j < i * other_mult; j = j + incr)
						num = num + incr;
				end
				num = num * 2;
			end
			operation = num;
		end
	endfunction

	localparam res = operation(4);
	output wire [31:0] out;
	assign out = res;
endmodule
