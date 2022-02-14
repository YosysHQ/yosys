module top;

    typedef struct packed {
        logic a;
        logic signed b;
        byte c;
        byte unsigned d;
        reg [3:0] e;
        reg signed [3:0] f;
        struct packed {
            logic a;
            logic signed b;
        } x;
        struct packed signed {
            logic a;
            logic signed b;
        } y;
    } S;
    S s;

    initial begin
        // test codegen for LHS
        s.a = '1;
        s.b = '1;
        s.c = '1;
        s.d = '1;
        s.e = '1;
        s.f = '1;
        s.x.a = '1;
        s.x.b = '1;
        s.y.a = '1;
        s.y.b = '1;
    end

`define CHECK(expr, width, signedness) \
    case (expr) \
        1'sb1: \
            case (expr) \
                2'sb11: if (!(signedness)) fail = 1; \
                default: if (signedness) fail = 1; \
            endcase \
        default: if (signedness) fail = 1; \
    endcase \
    case (expr) \
        1'b1: if ((width) != 1) fail = 1; \
        2'b11: if ((width) != 2) fail = 1; \
        3'b111: if ((width) != 3) fail = 1; \
        4'b1111: if ((width) != 4) fail = 1; \
        5'b1111_1: if ((width) != 5) fail = 1; \
        6'b1111_11: if ((width) != 6) fail = 1; \
        7'b1111_11: if ((width) != 7) fail = 1; \
        8'b1111_1111: if ((width) != 8) fail = 1; \
        9'b1111_1111_1: if ((width) != 9) fail = 1; \
        default: fail = 1; \
    endcase \
    begin \
        reg [9:0] indirect; \
        indirect = (expr); \
        if ((indirect != (expr)) != (signedness)) fail = 1; \
        indirect = $unsigned(expr); \
        if ($countones(indirect) != (width)) fail = 1; \
    end

    initial begin
        reg fail;
        fail = 0;

        `CHECK(s.a, 1, 0)
        `CHECK(s.b, 1, 1)
        `CHECK(s.c, 8, 1)
        `CHECK(s.d, 8, 0)
        `CHECK(s.e, 4, 0)
        `CHECK(s.f, 4, 1)

        `CHECK(s.x.a, 1, 0)
        `CHECK(s.x.b, 1, 1)
        `CHECK(s.y.a, 1, 0)
        `CHECK(s.y.b, 1, 1)

        `CHECK(s.x, 2, 0)
        `CHECK(s.y, 2, 1)

        assert (fail === 0);
    end


endmodule
