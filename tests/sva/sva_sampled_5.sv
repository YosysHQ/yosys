module top (input clk);
    typedef logic[3:0] cntr_t;
	logic init = 0;
	
    cntr_t cntr = 3;

`ifdef FAIL
	assert property (@(posedge clk ) 0 == 1);
`endif

	always_ff @(posedge clk) begin
	  init <= 1;
	  cntr <= cntr + 1;
`ifndef FAIL
	  if (!init) begin
		  assert ($sampled(cntr) == 3);
		  assert ($sampled(cntr) == cntr);

		  assert (cntr == $sampled(1 + 2));
		  assert (1'(cntr) != $sampled(1 + 2));
		  assert (3 == $sampled(1 + 2));
	  end
	  if (init) begin
	    assert (cntr == cntr_t'($sampled(cntr + 1)));
	    assert (cntr == $sampled(cntr + 1));
	    assert (cntr == $sampled(cntr) + 1);
	    assert (cntr == $sampled(cntr) + $sampled(1));
	    assert (1'(cntr) == 1'($sampled(cntr) + 1));
	    assert (1'(cntr) == $sampled(1'(cntr + 1)));
	  end
`endif
	end

endmodule
