module pass_through(
    input [63:0] inp,
    output [63:0] out
);
    assign out = inp;
endmodule

module top;
    logic [63:0] s0c, s1c, sxc, s0d, s1d, sxd, d;

    pass_through pt(8, d);

    assign s0c = '0 << 8;
    assign s1c = '1 << 8;
    assign sxc = 'x << 8;
    assign s0d = '0 << d;
    assign s1d = '1 << d;
    assign sxd = 'x << d;

    always @* begin
        assert (s0c === 64'h0000_0000_0000_0000);
        assert (s1c === 64'hFFFF_FFFF_FFFF_FF00);
        assert (sxc === 64'hxxxx_xxxx_xxxx_xx00);
        assert (s0d === 64'h0000_0000_0000_0000);
        assert (s1d === 64'hFFFF_FFFF_FFFF_FF00);
        assert (sxd === 64'hxxxx_xxxx_xxxx_xx00);
    end
endmodule
