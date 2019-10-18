module adff( input d, clk, clr, output reg q );
    initial begin
        q = 0;
    end
	  always @( posedge clk, posedge clr )
      if ( clr )
        q <= 1'b0;
      else
        q <= d;
endmodule

module adffn( input d, clk, clr, output reg q );
    initial begin
      q = 0;
    end
	  always @( posedge clk, negedge clr )
		  if ( !clr )
			  q <= 1'b0;
  		else
        q <= d;
endmodule

module dffs( input d, clk, pre, clr, output reg q );
    initial begin
      q = 0;
    end
    always @( posedge clk )
      if ( pre )
        q <= 1'b1;
      else
        q <= d;
endmodule

module ndffnr( input d, clk, pre, clr, output reg q );
    initial begin
      q = 0;
    end
    always @( negedge clk )
      if ( !clr )
        q <= 1'b0;
      else
        q <= d;
endmodule
