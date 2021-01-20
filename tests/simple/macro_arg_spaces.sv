module top(
	input wire [31:0] i,
	output wire [31:0] x, y, z
);

`define BAR(a) a
`define FOO(a = function automatic [31:0] f) a

`BAR(function automatic [31:0] a);
	input [31:0] i;
	a = i * 2;
endfunction

`FOO();
	input [31:0] i;
	f = i * 3;
endfunction

`FOO(function automatic [31:0] b);
	input [31:0] i;
	b = i * 5;
endfunction

assign x = a(i);
assign y = f(i);
assign z = b(i);

endmodule
