(* smtlib2_module *)
module smtlib2(a, b, add, sub, eq);
	input [7:0] a, b;
	(* smtlib2_comb_expr = "(bvadd a b)" *)
	output [7:0] add;
	(* smtlib2_comb_expr = "(bvadd a (bvneg b))" *)
	output [7:0] sub;
	(* smtlib2_comb_expr = "(= a b)" *)
	output eq;
endmodule

(* top *)
module uut;
	wire [7:0] a = $anyconst, b = $anyconst, add, sub, add2, sub2;
	wire eq;

	assign add2 = a + b;
	assign sub2 = a - b;

	smtlib2 s (
		.a(a),
		.b(b),
		.add(add),
		.sub(sub),
		.eq(eq)
	);

	always @* begin
		assert(add == add2);
		assert(sub == sub2);
		assert(eq == (a == b));
	end
endmodule
