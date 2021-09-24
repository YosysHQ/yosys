module dff ( input d, clk, output reg q );
	  always @( posedge clk )
        q <= d;
endmodule

module dffe( input d, clk, en, output reg q );
`ifndef NO_INIT
    initial begin
        q = 0;
    end
`endif
	  always @( posedge clk )
        if ( en )
              q <= d;
endmodule
