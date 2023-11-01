module top;
    integer x, y, z;
    task check;
        input integer a, b, c;
        assert (x == a);
        assert (y == b);
        assert (z == c);
    endtask
    always_comb begin
        x = 0; y = 0; z = 0;
        check(0, 0, 0);

        // post-increment/decrement statements
        x++;
        check(1, 0, 0);
        (* bar *) y (* foo *) ++;
        check(1, 1, 0);
        z--;
        check(1, 1, -1);
        (* bar *) z (* foo *) --;
        check(1, 1, -2);

        // pre-increment/decrement statements are equivalent
        ++z;
        check(1, 1, -1);
        (* bar *) ++ (* foo *) z;
        check(1, 1, 0);
        --x;
        check(0, 1, 0);
        (* bar *) -- (* foo *) y;
        check(0, 0, 0);

        // procedural pre-increment/decrement expressions
        z = ++x;
        check(1, 0, 1);
        z = ++ (* foo *) x;
        check(2, 0, 2);
        y = --x;
        check(1, 1, 2);
        y = -- (* foo *) x;

        // procedural post-increment/decrement expressions
        // TODO: support attributes on post-increment/decrement
        check(0, 0, 2);
        y = x++;
        check(1, 0, 2);
        y = x--;
        check(0, 1, 2);

        // procedural assignment expressions
        x = (y = (z = 99) + 1) + 1;
        check(101, 100, 99);
        x = (y *= 2);
        check(200, 200, 99);
        x = (z >>= 2) * 4;
        check(96, 200, 24);
        y = (z >>= 1'sb1) * 2; // shift is implicitly cast to unsigned
        check(96, 24, 12);

        // check width of post-increment expressions
        z = (y = 0);
        begin
            byte w;
            w = 0;
            x = {1'b1, ++w};
            check(257, 0, 0);
            assert (w == 1);
            x = {2'b10, w++};
            check(513, 0, 0);
            assert (w == 2);
        end
    end
endmodule
