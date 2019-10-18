module adff
    ( input d, clk, clr, output reg q );
    initial begin
      q = 0;
    end
	always @( posedge clk, posedge clr )
		if ( clr )
			q <= 1'b0;
		else
            q <= d;
endmodule

module adffn
    ( input d, clk, clr, output reg q );
    initial begin
      q = 0;
    end
	always @( posedge clk, negedge clr )
		if ( !clr )
			q <= 1'b0;
		else
            q <= d;
endmodule

module dffs
    ( input d, clk, pre, clr, output reg q );
    initial begin
      q = 0;
    end
	always @( posedge clk, posedge pre )
		if ( pre )
			q <= 1'b1;
		else
            q <= d;
endmodule

module ndffnr
    ( input d, clk, pre, clr, output reg q );
    initial begin
      q = 0;
    end
	always @( negedge clk, negedge pre )
		if ( !pre )
			q <= 1'b1;
		else
            q <= d;
endmodule

module top (
input clk,
input clr,
input pre,
input a,
output b,b1,b2,b3
);

dffs u_dffs (
        .clk (clk ),
        .clr (clr),
        .pre (pre),
        .d (a ),
        .q (b )
    );

ndffnr u_ndffnr (
        .clk (clk ),
        .clr (clr),
        .pre (pre),
        .d (a ),
        .q (b1 )
    );

adff u_adff (
        .clk (clk ),
        .clr (clr),
        .d (a ),
        .q (b2 )
    );

adffn u_adffn (
        .clk (clk ),
        .clr (clr),
        .d (a ),
        .q (b3 )
    );

endmodule
