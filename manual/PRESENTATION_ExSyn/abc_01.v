module test(input clk, a, b, c,
            output reg y);

	reg [2:0] q1, q2;
	always @(posedge clk) begin
		q1 <= { a, b, c };
		q2 <= q1;
		y <= ^q2;
	end
endmodule
