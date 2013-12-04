
module test_signed(a, b, c, d, y);

input [3:0] a, b, c;
input signed [3:0] d;
output reg [7:0] y;

always @* begin
	if (a && b)
		y = c;
	else
		y = d;
end

endmodule

module test_const(a, y);

input [3:0] a;
output reg [28:0] y;

always @*
	case (a)
		4'b0000: y = 0;
		4'b0001: y = 11;
		4'b0010: y = 222;
		4'b0011: y = 3456;
		4'b0100: y = 'b10010010;
		4'b0101: y = 'h123abc;
		4'b0110: y = 'o1234567;
		4'b0111: y = 'd3456789;
		4'b1000: y = 16'b10010010;
		4'b1001: y = 16'h123abc;
		4'b1010: y = 16'o1234567;
		4'b1011: y = 16'd3456789;
		4'b1100: y = { "foo", "bar" };
		4'b1101: y = "foobarfoobarfoobar";
		4'b1110: y = 16'h1;
		4'b1111: y = a;
		default: y = 'bx;
	endcase

endmodule

