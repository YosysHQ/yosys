module top (input logic clock, ctrl);
	logic read, write, ready;

	demo uut (
		.clock(clock),
		.ctrl(ctrl)
	);

	assign read = uut.read;
	assign write = uut.write;
	assign ready = uut.ready;

	a_rw: assert property ( @(posedge clock) !(read && write) );
`ifdef FAIL
	a_wr: assert property ( @(posedge clock) write |-> ready );
`else
	a_wr: assert property ( @(posedge clock) write |=> ready );
`endif
endmodule
