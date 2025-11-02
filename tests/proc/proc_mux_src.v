module nested(
	input clk,
	input [7:0] A,
	input [7:0] B,
	input [3:0] mode1,
	input [3:0] mode2,
	output reg [7:0] result1,
	output reg [7:0] result2,
	output reg [1:0] arith
);

	localparam OP_A = 4'b0000;
	localparam OP_BA = 4'b0001;
	localparam OP_BB = 4'b0010;
	localparam OP_C = 4'b0011;

	always @(posedge clk)
	begin
		case (mode1)
			OP_A: begin
				result1 = A + B;
				result2 = A - B;
				arith = 2'b01;
			end
			OP_BA , OP_BB : begin
				result1 = A * B;
				result2 = A / B;
				arith = 2'b00;
			end
			OP_C : begin
				arith = 2'b10;
				case (mode2)
					OP_A: begin
						result1 = ~B;
						result2 = B;
					end
					OP_C: begin
						result1 = A ^ B;
						result2 = A == B;
					end
					default: begin
						result1 = 1'b0;
						// result2 omitted
					end
				endcase
			end
			default: begin
				result1 = 8'b0;
				result2 = 8'b0;
				arith = 2'b11;
			end
		endcase
	end
endmodule

module tiny(
	input clk,
	input ya,
	input [7:0] in,
	output reg [7:0] out,
);
	always @(posedge clk)
	begin
		case (ya)
			1'b1: begin
				out = in;
			end
		endcase
	end
endmodule

module tiny2(
	input clk,
	input [1:0] ya,
	input [7:0] in,
	output reg [7:0] out,
);
	always @(posedge clk)
	begin
		case (ya)
			2'b01: begin
				out = in;
			end
			2'b10: begin
				out = 1'b1;
			end
			default begin
				out = 1'b0;
			end
		endcase
	end
endmodule
