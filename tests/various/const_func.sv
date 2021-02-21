module Example(outA, outB, outC, outD);
    parameter OUTPUT = "FOO";
    output wire [23:0] outA;
    output wire [23:0] outB;
    output reg outC, outD;
    function automatic [23:0] flip;
        input [23:0] inp;
        flip = ~inp;
    endfunction

    generate
        if (flip(OUTPUT) == flip("BAR"))
            assign outA = OUTPUT;
        else
            assign outA = 0;

        case (flip(OUTPUT))
            flip("FOO"): assign outB = OUTPUT;
            flip("BAR"): assign outB = 0;
            flip("BAZ"): assign outB = "HI";
        endcase

        genvar i;
        initial outC = 0;
        for (i = 0; i != flip(flip(OUTPUT[15:8])); i = i + 1)
            if (i + 1 == flip(flip("O")))
                initial outC = 1;
    endgenerate

    integer j;
    initial begin
        outD = 1;
        for (j = 0; j != flip(flip(OUTPUT[15:8])); j = j + 1)
            if (j + 1 == flip(flip("O")))
                outD = 0;
    end
endmodule

module top(out);
    wire [23:0] a1, a2, a3, a4;
    wire [23:0] b1, b2, b3, b4;
    wire        c1, c2, c3, c4;
    wire        d1, d2, d3, d4;
    Example          e1(a1, b1, c1, d1);
    Example #("FOO") e2(a2, b2, c2, d2);
    Example #("BAR") e3(a3, b3, c3, d3);
    Example #("BAZ") e4(a4, b4, c4, d4);

    output wire [24 * 8 - 1 + 4 :0] out;
    assign out = {
        a1, a2, a3, a4,
        b1, b2, b3, b4,
        c1, c2, c3, c4,
        d1, d2, d3, d4};

    function signed [31:0] negate;
        input integer inp;
        negate = ~inp;
    endfunction
    parameter W = 10;
    parameter X = 3;
    localparam signed Y = $floor(W / X);
    localparam signed Z = negate($floor(W / X));

    always_comb begin
        assert(a1 == 0);
        assert(a2 == 0);
        assert(a3 == "BAR");
        assert(a4 == 0);
        assert(b1 == "FOO");
        assert(b2 == "FOO");
        assert(b3 == 0);
        assert(b4 == "HI");
        assert(c1 == 1);
        assert(c2 == 1);
        assert(c3 == 0);
        assert(c4 == 0);
        assert(d1 == 0);
        assert(d2 == 0);
        assert(d3 == 1);
        assert(d4 == 1);

        assert(Y == 3);
        assert(Z == ~3);
    end
endmodule
