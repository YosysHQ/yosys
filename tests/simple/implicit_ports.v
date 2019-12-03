// Test implicit port connections
module alu (input [2:0] a, input [2:0] b, input cin, output cout, output [2:0] result);
	assign cout = cin;
	assign result = a + b;
endmodule

module named_ports(input [2:0] a, b, output [2:0] alu_result, output cout);
	wire cin = 1;
	alu alu (
		.a(a),
		.b, // Implicit connection is equivalent to .b(b)
		.cin(), // Explicitely unconnected
		.cout(cout),
		.result(alu_result)
	);
endmodule
