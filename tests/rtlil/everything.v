module alu(
	input clk,
	input [7:0] A,
	input [7:0] B,
	input [3:0] operation,
	output reg [7:0] result,
	output reg CF,
	output reg ZF,
	output reg SF
);

	localparam ALU_OP_ADD = 4'b0000;
	localparam ALU_OP_SUB = 4'b0001;

	reg [8:0] tmp;

	always @(posedge clk)
	begin
		case (operation)
			ALU_OP_ADD :
				tmp = A + B;
			ALU_OP_SUB :
				tmp = A - B;
		endcase

		CF <= tmp[8];
		ZF <= tmp[7:0] == 0;
		SF <= tmp[7];

		result <= tmp[7:0];
	end
endmodule

module foo(
    input [7:0] a, input [7:0] b, output [7:0] y
);
    wire [7:0] bb;
    assign b = bb;
    assign y = a + bb;
endmodule
