module m(input a, output y1, output y2);
	assign y1 = a;
	assign y2 = a;
endmodule

module top(input a, output y2, output y1);
	m inst(.a(a), .y1(y1), .y2(y2));
endmodule
