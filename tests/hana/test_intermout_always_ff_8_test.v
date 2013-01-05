module NegEdgeClock(q, d, clk, reset);
input d, clk, reset;
output reg q;

always @(negedge clk or negedge reset)
    if(!reset)
	    q <= 1'b0;
	else	
        q <= d;

endmodule
