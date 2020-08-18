module top(out);
	function integer operation;
		input integer num;
		begin
			operation = 0;
			begin : op_i
				integer i;
				for (i = 0; i < 2; i = i + 1)
				begin : op_j
					integer j;
					for (j = i; j < i * 2; j = j + 1)
						num = num + 1;
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
