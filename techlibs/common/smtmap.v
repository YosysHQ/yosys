(* techmap_celltype = "$pmux" *)
module smt_pmux (A, B, S, Y);
	parameter WIDTH = 1;
	parameter S_WIDTH = 1;

	(* force_downto *)
	input [WIDTH-1:0] A;
	(* force_downto *)
	input [WIDTH*S_WIDTH-1:0] B;
	(* force_downto *)
	input [S_WIDTH-1:0] S;
	(* force_downto *)
	output [WIDTH-1:0] Y;

	(* force_downto *)
	wire [WIDTH-1:0] Y_B;

	genvar i, j;
	generate
		(* force_downto *)
		wire [WIDTH*(S_WIDTH+1)-1:0] C;

		assign C[WIDTH-1:0] = A;
		for (i = 0; i < S_WIDTH; i = i + 1)
			assign C[WIDTH*(i+2)-1:WIDTH*(i+1)] = S[i] ? B[WIDTH*(i+1)-1:WIDTH*i] : C[WIDTH*(i+1)-1:WIDTH*i];
		assign Y = C[WIDTH*(S_WIDTH+1)-1:WIDTH*S_WIDTH];
	endgenerate
endmodule
