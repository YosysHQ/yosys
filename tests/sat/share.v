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


module test_3(
	input [3:0] s,
	input [7:0] a, b, c,
	output reg [7:0] y0,
	output reg [7:0] y1,
	output reg [7:0] y2,
	output reg [7:0] y3,
);
	wire is_onehot = s & (s - 1);

	always @* begin
		y0 <= 0;
		y1 <= 0;
		y2 <= 0;
		y3 <= 0;
		if (s < 3) y0 <= b / c;
		if (3 <= s && s < 6) y1 <= c / b;
		if (6 <= s && s < 9) y2 <= a / b;
		if (9 <= s && s < 12) y3 <= b / a;
	end
endmodule

