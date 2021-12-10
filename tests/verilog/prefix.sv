module top;
    genvar i, j;
    if (1) begin : blk1
        integer a = 1;
        for (i = 0; i < 2; i = i + 1) begin : blk2
            integer b = i;
            for (j = 0; j < 2; j = j + 1) begin : blk3
                integer c = j;
                localparam x = i;
                localparam y = j;
                always @* begin
                    assert (1 == a);
                    assert (1 == blk1.a);
                    assert (1 == top.blk1.a);
                    assert (i == b);
                    assert (i == blk2[i].b);
                    assert (i == blk1.blk2[i].b);
                    assert (i == top.blk1.blk2[i].b);
                    assert (i == blk2[x].b);
                    assert (i == blk1.blk2[x].b);
                    assert (i == top.blk1.blk2[x].b);
                    assert (j == c);
                    assert (j == blk3[j].c);
                    assert (j == blk2[x].blk3[j].c);
                    assert (j == blk1.blk2[x].blk3[j].c);
                    assert (j == top.blk1.blk2[x].blk3[j].c);
                    assert (j == c);
                    assert (j == blk3[y].c);
                    assert (j == blk2[x].blk3[y].c);
                    assert (j == blk1.blk2[x].blk3[y].c);
                    assert (j == top.blk1.blk2[x].blk3[y].c);
                    assert (j == top.blk1.blk2[x].blk3[y].c[0]);
                    assert (0 == top.blk1.blk2[x].blk3[y].c[1]);
                    assert (0 == top.blk1.blk2[x].blk3[y].c[j]);
                end
            end
            always @* begin
                assert (1 == a);
                assert (1 == blk1.a);
                assert (1 == top.blk1.a);
                assert (i == b);
                assert (i == blk2[i].b);
                assert (i == blk1.blk2[i].b);
                assert (i == top.blk1.blk2[i].b);
                assert (0 == blk3[0].c);
                assert (0 == blk2[i].blk3[0].c);
                assert (0 == blk1.blk2[i].blk3[0].c);
                assert (0 == top.blk1.blk2[i].blk3[0].c);
                assert (1 == blk3[1].c);
                assert (1 == blk2[i].blk3[1].c);
                assert (1 == blk1.blk2[i].blk3[1].c);
                assert (1 == top.blk1.blk2[i].blk3[1].c);
            end
        end
        always @* begin
            assert (1 == a);
            assert (1 == blk1.a);
            assert (1 == top.blk1.a);
            assert (0 == blk2[0].b);
            assert (0 == blk1.blk2[0].b);
            assert (0 == top.blk1.blk2[0].b);
            assert (1 == blk2[1].b);
            assert (1 == blk1.blk2[1].b);
            assert (1 == top.blk1.blk2[1].b);
            assert (0 == blk2[0].blk3[0].c);
            assert (0 == blk1.blk2[0].blk3[0].c);
            assert (0 == top.blk1.blk2[0].blk3[0].c);
            assert (1 == blk2[0].blk3[1].c);
            assert (1 == blk1.blk2[0].blk3[1].c);
            assert (1 == top.blk1.blk2[0].blk3[1].c);
            assert (0 == blk2[1].blk3[0].c);
            assert (0 == blk1.blk2[1].blk3[0].c);
            assert (0 == top.blk1.blk2[1].blk3[0].c);
            assert (1 == blk2[1].blk3[1].c);
            assert (1 == blk1.blk2[1].blk3[1].c);
            assert (1 == top.blk1.blk2[1].blk3[1].c);
        end
    end
    always @* begin
        assert (1 == blk1.a);
        assert (1 == top.blk1.a);
        assert (0 == blk1.blk2[0].b);
        assert (0 == top.blk1.blk2[0].b);
        assert (1 == blk1.blk2[1].b);
        assert (1 == top.blk1.blk2[1].b);
        assert (0 == blk1.blk2[0].blk3[0].c);
        assert (0 == top.blk1.blk2[0].blk3[0].c);
        assert (1 == blk1.blk2[0].blk3[1].c);
        assert (1 == top.blk1.blk2[0].blk3[1].c);
        assert (0 == blk1.blk2[1].blk3[0].c);
        assert (0 == top.blk1.blk2[1].blk3[0].c);
        assert (1 == blk1.blk2[1].blk3[1].c);
        assert (1 == top.blk1.blk2[1].blk3[1].c);
    end
endmodule
