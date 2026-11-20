module top (input clk);
	reg [3:0] cyc = 0;
	reg rst_n = 0, ack = 0;
	always @(posedge clk) begin
		if (cyc != 15) cyc <= cyc + 1;
		rst_n <= rst_n | (cyc == 3);
	end
	always @(posedge clk) if (!rst_n) ack <= 0; else ack <= 1;
`ifdef FAIL
  assert property (@(posedge clk) 0);
`else
	assert property (@(posedge clk) disable iff ($sampled(!rst_n)) 1'b1 |=> ack);
`endif
endmodule
