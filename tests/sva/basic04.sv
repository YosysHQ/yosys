module top_properties (input logic clock, read, write, ready);
	a_rw: assert property ( @(posedge clock) !(read && write) );
	a_wr: assert property ( @(posedge clock) write |-> ready );
endmodule

bind top top_properties properties_inst (.*);
