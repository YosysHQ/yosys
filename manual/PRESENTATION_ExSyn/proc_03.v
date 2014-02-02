module test(input A, B, C, D, E,
            output reg Y);
    always @* begin
	Y <= A;
	if (B)
	    Y <= C;
	if (D)
	    Y <= E;
    end
endmodule
