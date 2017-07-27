module top (input logic clock, ctrl);
	logic read = 0, write = 0, ready = 0;

	always @(posedge clock) begin
		read <= !ctrl;
		write <= ctrl;
		ready <= write;
	end
endmodule

module top_properties (input logic clock, read, write, ready);
	a_rw: assert property ( @(posedge clock) !(read && write) );
`ifdef FAIL
	a_wr: assert property ( @(posedge clock) write |-> ready );
`else
	a_wr: assert property ( @(posedge clock) write |=> ready );
`endif
endmodule

bind top top_properties properties_inst (.*);
