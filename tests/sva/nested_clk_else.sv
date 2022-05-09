module top (input clk, a, b);
	always @(posedge clk) begin
        if (a);
        else assume property (@(posedge clk) b);
	end

`ifndef FAIL
    assume property (@(posedge clk) !a);
`endif
    assert property (@(posedge clk) b);
endmodule
