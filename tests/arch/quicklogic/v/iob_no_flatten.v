module my_dff ( input d, clk, output reg q );
    initial q <= 1'b0;
    always @( posedge clk )
        q <= d;
endmodule

module my_top (
    inout  wire pad,
    input  wire i,
    input  wire t,
    output wire o,
    input  wire clk
);

    wire i_r;
    wire t_r;
    wire o_r;

    // IOB
    assign pad = (t_r) ? i_r : 1'bz;
    assign o_r = pad;

    // DFFs
    my_dff dff_i (i,   clk, i_r);
    my_dff dff_t (t,   clk, t_r);
    my_dff dff_o (o_r, clk, o);

endmodule
