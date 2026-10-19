module test_case (
	input wire clk,
	input wire rst_n,
	input wire in_val,
	output wire out_a,
	output wire out_b,
	output wire out_c,
	output wire out_d
);
	reg a, b, c, d;

	always @(posedge clk) begin
		if (!rst_n) begin
			a <= 1'b0;
			b <= 1'b0;
			c <= 1'b0;
			d <= 1'b0;
		end else begin
			a <= c & in_val;
			b <= d & in_val;
			c <= b | in_val;
			d <= a | in_val;
		end
	end

	assign out_a = a;
	assign out_b = b;
	assign out_c = c;
	assign out_d = d;
endmodule
