module latchp
    ( input d, clk, en, output reg q );
	always @*
		if ( en )
			q <= d;
endmodule

module latchn
    ( input d, clk, en, output reg q );
	always @*
		if ( !en )
			q <= d;
endmodule

module latchsr
    ( input d, clk, en, clr, pre, output reg q );
	always @*
		if ( clr )
			q <= 1'b0;
		else if ( pre )
			q <= 1'b1;
		else if ( en )
			q <= d;
endmodule


module top (
input clk,
input clr,
input pre,
input a,
output b,b1,b2
);


latchp u_latchp (
        .en (clk ),
        .d (a ),
        .q (b )
    );


latchn u_latchn (
        .en (clk ),
        .d (a ),
        .q (b1 )
    );


latchsr u_latchsr (
        .en (clk ),
        .clr (clr),
        .pre (pre),
        .d (a ),
        .q (b2 )
    );

endmodule
