(* blackbox *)
module bb(output y);
endmodule

// all instances of `m` tie together a[1], a[2]
// this can be used to conclude y[0]=0
module m(input [3:0] a, output [1:0] y, output x);
	assign y[0] = a[1] != a[2];
	assign x = a[0] ^ a[3];
	(* should_get_optimized_out *)
	bb bb1(.y(y[1]));
endmodule

module top(input j, output z, output [2:0] x);
	wire [1:0] y1;
	wire [1:0] y2;
	wire [1:0] y3;
	m inst1(.a(0), .y(y1), .x(x[0]));
	m inst2(.a(15), .y(y2), .x(x[1]));
	m inst3(.a({1'b1, j, j, 1'b0}), .y(y3), .x(x[2]));
	assign z = (&y1) ^ (&y2) ^ (&y3);
endmodule
