
// test cases found using vloghammer
// https://github.com/cliffordwolf/VlogHammer

module test01(a, y);
	input [7:0] a;
	output [3:0] y;
	assign y = ~a >> 4;
endmodule

