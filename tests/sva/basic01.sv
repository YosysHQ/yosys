module top (input logic clock, ctrl);
	logic read = 0, write = 0, ready = 0;

	always @(posedge clock) begin
		read <= !ctrl;
		write <= ctrl;
		ready <= write;
	end

	a_rw: assert property ( @(posedge clock) !(read && write) );
`ifdef FAIL
	a_wr: assert property ( @(posedge clock) write |-> ready );
`else
	a_wr: assert property ( @(posedge clock) write |=> ready );
`endif
endmodule
