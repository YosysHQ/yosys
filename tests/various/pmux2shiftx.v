module pmux2shiftx_test (
	input [2:0] S1,
	input [5:0] S2,
	input [9:0] A, B, C, D, D, E, F,
	input [9:0] G, H, I, J, K, L, M, N,
	output reg [9:0] X
);
	always @* begin
		case (S1)
			3'd0: X = A;
			3'd1: X = B;
			3'd2: X = C;
			3'd3: X = D;
			3'd4: X = E;
			3'd5: X = F;
			3'd6: X = G;
			3'd7: X = H;
		endcase
		case (S2)
			6'd46: X = I;
			6'd47: X = J;
			6'd48: X = K;
			6'd52: X = L;
			6'd53: X = M;
			6'd54: X = N;
		endcase
	end
endmodule
