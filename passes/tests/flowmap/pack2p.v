// Like pack2.v, but results in a simpler network.
module top(...);
	(* $flowmap_level=1 *) input a;
	(* $flowmap_level=1 *) input b;
	(* $flowmap_level=2 *) input c;
	(* $flowmap_level=1 *) input d;
	(* $flowmap_level=3 *) input e;
	(* $flowmap_level=1 *) input f;
	wire u = a&b;
	wire w = c|d;
	wire v = u|w;
	wire n0 = w&e;
	wire n1 = n0|f;
	output n2 = v&n1;
endmodule
