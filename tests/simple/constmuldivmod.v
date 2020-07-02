module constmuldivmod(input [7:0] A, input [5:0] mode, output reg [7:0] Y);
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

			15: Y = $signed(A) / $signed(8'd0);
			16: Y = $signed(A) % $signed(8'd0);
			17: Y = $signed(A) * $signed(8'd0);

			18: Y = $signed(A) / $signed(8'd1);
			19: Y = $signed(A) % $signed(8'd1);
			20: Y = $signed(A) * $signed(8'd1);

			21: Y = $signed(A) / $signed(8'd2);
			22: Y = $signed(A) % $signed(8'd2);
			23: Y = $signed(A) * $signed(8'd2);

			24: Y = $signed(A) / $signed(8'd4);
			25: Y = $signed(A) % $signed(8'd4);
			26: Y = $signed(A) * $signed(8'd4);

			27: Y = $signed(A) / $signed(8'd8);
			28: Y = $signed(A) % $signed(8'd8);
			29: Y = $signed(A) * $signed(8'd8);

			30: Y = $signed(A) / $signed(-8'd0);
			31: Y = $signed(A) % $signed(-8'd0);
			32: Y = $signed(A) * $signed(-8'd0);

			33: Y = $signed(A) / $signed(-8'd1);
			34: Y = $signed(A) % $signed(-8'd1);
			35: Y = $signed(A) * $signed(-8'd1);

			36: Y = $signed(A) / $signed(-8'd2);
			37: Y = $signed(A) % $signed(-8'd2);
			38: Y = $signed(A) * $signed(-8'd2);

			39: Y = $signed(A) / $signed(-8'd4);
			40: Y = $signed(A) % $signed(-8'd4);
			41: Y = $signed(A) * $signed(-8'd4);

			42: Y = $signed(A) / $signed(-8'd8);
			43: Y = $signed(A) % $signed(-8'd8);
			44: Y = $signed(A) * $signed(-8'd8);

			default: Y = 8'd16 * A;
		endcase
	end
endmodule
