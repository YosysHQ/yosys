module AND(input [7:0] A, B, output [7:0] Y);
	ALU #(.MODE("AND")) _TECHMAP_REPLACE_ (.A(A), .B(B), .Y(Y));
endmodule
