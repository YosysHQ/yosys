// Test implicit port connections
module alu (input [2:0] a, input [2:0] b, input cin, output cout, output [2:0] result);
	assign cout = cin;
	assign result = a + b;
endmodule

module named_ports(output [2:0] alu_result, output cout);
	wire [2:0] a = 3'b010, b = 3'b100;
	wire cin = 1;

	alu alu (
		.a(a),
		.b, // Implicit connection is equivalent to .b(b)
		.cin(), // Explicitely unconnected
		.cout(cout),
		.result(alu_result)
	);
endmodule

