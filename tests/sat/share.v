module test_1(
	input [7:0] a, b, c,
	input s, x,
	output [7:0] y1, y2
);
	wire [7:0] t1, t2;
	assign t1 = s ? a*b : 0, t2 = !s ? b*c : 0;
	assign y1 = x ? t2 : t1, y2 = x ? t1 : t2;
endmodule


module test_2(
	input s,
	input [7:0] a, b, c,
	output reg [7:0] y
);
	always @* begin
		y <= 'bx;
		if (s) begin
			if (a * b > 8)
				y <= b / c;
			else
				y <= c / b;
		end else begin
			if (b * c > 8)
				y <= a / b;
			else
				y <= b / a;
		end
	end
endmodule

