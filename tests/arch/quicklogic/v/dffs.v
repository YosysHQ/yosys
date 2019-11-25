module my_dff ( input d, clk, output reg q );
    initial q <= 1'b0;
    always @( posedge clk )
        q <= d;
endmodule

module my_dffc ( input d, clk, clr, output reg q );
    initial q <= 1'b0;
    always @( posedge clk or posedge clr )
        if ( clr )
            q <= 1'b0;
        else
            q <= d;
endmodule

module my_dffp ( input d, clk, pre, output reg q );
    initial q <= 1'b0;
    always @( posedge clk or posedge pre )
        if ( pre )
            q <= 1'b1;
        else
            q <= d;
endmodule

