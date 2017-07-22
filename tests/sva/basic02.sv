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
	a_wr: assert property ( @(posedge clock) write |-> ready );
endmodule

bind top top_properties inst (.*);
