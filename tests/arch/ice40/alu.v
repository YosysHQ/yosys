module top (
	input clock,
	input [31:0] dinA, dinB,
	input [2:0] opcode,
	output reg [31:0] dout
);
	always @(posedge clock) begin
		case (opcode)
		0: dout <= dinA + dinB;
		1: dout <= dinA - dinB;
		2: dout <= dinA >> dinB;
		3: dout <= $signed(dinA) >>> dinB;
		4: dout <= dinA << dinB;
		5: dout <= dinA & dinB;
		6: dout <= dinA | dinB;
		7: dout <= dinA ^ dinB;
		endcase
	end
endmodule
