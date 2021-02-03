`define CONSTANT_CHECK \
	if (WIDTH === 'bx) begin \
		$display("FAIL"); \
		$finish; \
	end

module top;
	parameter WIDTH = 32;
	integer j;
	initial begin
		`CONSTANT_CHECK
		if (WIDTH == 32) begin : procedural_conditional_block
			`CONSTANT_CHECK
		end
		case (WIDTH)
			32: `CONSTANT_CHECK
			default: ;
		endcase
		for (j = 0; j < 2; j = j + 1) begin : procedural_loop_block
			`CONSTANT_CHECK
		end
	end
	generate
		if (WIDTH == 32) begin : conditional_block
			initial `CONSTANT_CHECK
		end
		case (WIDTH)
			32: initial `CONSTANT_CHECK
			default: ;
		endcase
		genvar i;
		for (i = 0; i < 2; i = i + 1) begin : loop_block
			initial `CONSTANT_CHECK
		end
	endgenerate
endmodule
