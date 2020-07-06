module constmuldivmod(input [7:0] A, input [2:0] mode, output reg [7:0] Y);
	always @* begin
		case (mode)
			0: Y = A / 8'd0;
			1: Y = A % 8'd0;
			2: Y = A * 8'd0;

			3: Y = A / 8'd1;
			4: Y = A % 8'd1;
			5: Y = A * 8'd1;

			6: Y = A / 8'd2;
			7: Y = A % 8'd2;
			8: Y = A * 8'd2;

			9: Y = A / 8'd4;
			10: Y = A % 8'd4;
			11: Y = A * 8'd4;

			12: Y = A / 8'd8;
			13: Y = A % 8'd8;
			14: Y = A * 8'd8;

			default: Y = 8'd16 * A;
		endcase
	end
endmodule
