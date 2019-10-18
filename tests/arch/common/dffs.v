module dff ( input d, clk, output reg q );
	  always @( posedge clk )
        q <= d;
endmodule

module dffe( input d, clk, en, output reg q );
    initial begin
        q = 0;
    end
	  always @( posedge clk )
        if ( en )
              q <= d;
endmodule
