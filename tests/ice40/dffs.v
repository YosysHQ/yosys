module dff
    ( input d, clk, output reg q );
	always @( posedge clk )
            q <= d;
endmodule

module dffe
    ( input d, clk, en, output reg q );
    initial begin
      q = 0;
    end
	always @( posedge clk )
		if ( en )
			q <= d;
endmodule

module top (
input clk,
input en,
input a,
output b,b1,
);

dff u_dff (
        .clk (clk ),
        .d (a ),
        .q (b )
    );

dffe u_ndffe (
        .clk (clk ),
        .en (en),
        .d (a ),
        .q (b1 )
    );

endmodule
