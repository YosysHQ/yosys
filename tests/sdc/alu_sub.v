module adder(
    input [7:0] a, input [7:0] b, output [7:0] y
);
    assign y = a + b;
endmodule

module wrapper(
	input clk,
	input [7:0] A,
	input [7:0] B,
	input [3:0] op,
	output reg [7:0] result
);
	wire CF, ZF, SF;
	alu alu(
		.clk(clk),
		.A(A),
		.B(B),
		.operation(op),
		.result(result),
		.CF(CF),
		.ZF(ZF),
		.SF(SF)
	);
endmodule

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

	localparam ALU_OP_ADD /* verilator public_flat */ = 4'b0000;
	localparam ALU_OP_SUB /* verilator public_flat */ = 4'b0001;

	reg [8:0] tmp;
	reg [7:0] added;

	adder adder(.a(A), .b(B), .y(added));

	always @(posedge clk)
	begin
		case (operation)
			ALU_OP_ADD :
				tmp = added;
			ALU_OP_SUB :
				tmp = A - B;
		endcase

		CF <= tmp[8];
		ZF <= tmp[7:0] == 0;
		SF <= tmp[7];

		result <= tmp[7:0];
	end
endmodule

