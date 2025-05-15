module m;
parameter PARAM = 0;
endmodule

(* foo="bar" *)
(* val=32'hffffffff *)
module top;
	(* dont_touch *)
	wire w;

	m #(.PARAM(-3)) inst();
endmodule
