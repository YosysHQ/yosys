module top(
	input wire x,
	output reg y
);
	always @* begin
		case (top.x)
			1: top.y = 0;
			0: top.y = 1;
		endcase
	end
endmodule
