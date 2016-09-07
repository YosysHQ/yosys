// Demo for assertpmux

module demo6 (input A, B, C, D, E, output reg Y);
	always @* begin
		Y = 0;
		if (A != B) begin
			(* parallel_case *)
			case (C)
				A: Y = D;
				B: Y = E;
			endcase
		end
	end
endmodule
