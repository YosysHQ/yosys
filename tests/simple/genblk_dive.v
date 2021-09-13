`default_nettype none
module top(output wire x);
	generate
		if (1) begin : Z
			if (1) begin : A
				wire x;
				if (1) begin : B
					wire x;
					if (1) begin : C
						wire x;
						assign B.x = 0;
						wire z = A.B.C.x;
					end
					assign A.x = A.B.C.x;
				end
				assign B.C.x = B.x;
			end
		end
	endgenerate
	assign x = Z.A.x;
endmodule
