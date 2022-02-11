module module_scope_case_top(
	input wire x,
	output reg y
);
	always @* begin
		case (module_scope_case_top.x)
			1: module_scope_case_top.y = 0;
			0: module_scope_case_top.y = 1;
		endcase
	end
endmodule
