module json_param_defaults #(
	parameter WIDTH = 8,
	parameter SIGNED = 1
) (
	input  [WIDTH-1:0] a,
	output [WIDTH-1:0] y
);
	wire [WIDTH-1:0] y_int = a << SIGNED;
	assign y = y_int;
endmodule
