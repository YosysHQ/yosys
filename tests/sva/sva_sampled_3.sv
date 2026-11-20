module top (input clk);
    typedef logic[10:0] cntr_t;
	logic init = 0;
    cntr_t cntr = 3;

	always_ff @(posedge clk) begin
		init <= 1;
		cntr <= cntr + 1;
		if (init) begin
`ifdef FAIL
		  assert (cntr != cntr_t'($sampled(cntr) + 1));
`else
		  assert (cntr == cntr_t'($sampled(cntr) + 1));
`endif
	  end
	end
endmodule
