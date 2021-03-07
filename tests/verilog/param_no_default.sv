module example #(
    parameter w,
    parameter x = 1,
    parameter byte y,
    parameter byte z = 3
) (
    output a, b,
    output byte c, d
);
    assign a = w;
    assign b = x;
    assign c = y;
    assign d = z;
endmodule

module top;
    wire a1, b1;
    wire a2, b2;
    wire a3, b3;
    wire a4, b4;
    byte c1, d1;
    byte c2, d2;
    byte c3, d3;
    byte c4, d4;

    example #(0, 1, 2) e1(a1, b1, c1, d1);
    example #(.w(1), .y(4)) e2(a2, b2, c2, d2);
    example #(.x(0), .w(1), .y(5)) e3(a3, b3, c3, d3);
    example #(1, 0, 9, 10) e4(a4, b4, c4, d4);

    always @* begin
        assert (a1 == 0);
        assert (b1 == 1);
        assert (c1 == 2);
        assert (d1 == 3);

        assert (a2 == 1);
        assert (b2 == 1);
        assert (c2 == 4);
        assert (d3 == 3);

        assert (a3 == 1);
        assert (b3 == 0);
        assert (c3 == 5);
        assert (d3 == 3);

        assert (a4 == 1);
        assert (b4 == 0);
        assert (c4 == 9);
        assert (d4 == 10);
    end
endmodule
