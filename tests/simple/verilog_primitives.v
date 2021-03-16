module verilog_primitives (
	input wire in1, in2, in3,
	output wire out_buf0, out_buf1, out_buf2, out_buf3, out_buf4,
	output wire out_not0, out_not1, out_not2,
	output wire out_xnor
);

buf u_buf0 (out_buf0, in1);
buf u_buf1 (out_buf1, out_buf2, out_buf3, out_buf4, in2);

not u_not0 (out_not0, out_not1, out_not2, in1);

xnor u_xnor0 (out_xnor, in1, in2, in3);

endmodule
