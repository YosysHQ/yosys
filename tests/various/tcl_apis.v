module m;
parameter PARAM = 0;
endmodule

(* foo="bar" *)
module top;
	(* dont_touch *)
	wire w;

	m #(.PARAM(4)) inst();
endmodule
