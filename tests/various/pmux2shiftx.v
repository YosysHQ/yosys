module pmux2shiftx_test (
	input [2:0] S1,
	input [5:0] S2,
	input [1:0] S3,
	input [9:0] A, B, C, D, D, E, F, G, H,
	input [9:0] I, J, K, L, M, N, O, P, Q,
	output reg [9:0] X
);
	always @* begin
		case (S1)
			3'd 0: X = A;
			3'd 1: X = B;
			3'd 2: X = C;
			3'd 3: X = D;
			3'd 4: X = E;
			3'd 5: X = F;
			3'd 6: X = G;
			3'd 7: X = H;
		endcase
		case (S2)
			6'd 45: X = I;
			6'd 47: X = J;
			6'd 49: X = K;
			6'd 55: X = L;
			6'd 57: X = M;
			6'd 59: X = N;
		endcase
		case (S3)
			2'd 1: X = O;
			2'd 2: X = P;
			2'd 3: X = Q;
		endcase
	end
endmodule

module issue01135(input [7:0] i, output reg o);
always @*
case (i[6:3])
    4: o <= i[0];
    3: o <= i[2];
    7: o <= i[3];
    default: o <= 1'b0;
endcase
endmodule
