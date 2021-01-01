module gate(
    off, fib0, fib1, fib2, fib3, fib4, fib5, fib6, fib7, fib8, fib9
);
    input wire signed [31:0] off;

    function automatic integer fib(
        input integer k
    );
        if (k == 0)
            fib = 0;
        else if (k == 1)
            fib = 1;
        else
            fib = fib(k - 1) + fib(k - 2);
    endfunction

    function automatic integer fib_wrap(
        input integer k,
        output integer o
    );
        o = off + fib(k);
    endfunction

    output integer fib0;
    output integer fib1;
    output integer fib2;
    output integer fib3;
    output integer fib4;
    output integer fib5;
    output integer fib6;
    output integer fib7;
    output integer fib8;
    output integer fib9;

    initial begin : blk
        integer unused;
        unused = fib_wrap(0, fib0);
        unused = fib_wrap(1, fib1);
        unused = fib_wrap(2, fib2);
        unused = fib_wrap(3, fib3);
        unused = fib_wrap(4, fib4);
        unused = fib_wrap(5, fib5);
        unused = fib_wrap(6, fib6);
        unused = fib_wrap(7, fib7);
        unused = fib_wrap(8, fib8);
        unused = fib_wrap(9, fib9);
    end
endmodule

module gold(
    off, fib0, fib1, fib2, fib3, fib4, fib5, fib6, fib7, fib8, fib9
);
    input wire signed [31:0] off;

    output integer fib0 = off + 0;
    output integer fib1 = off + 1;
    output integer fib2 = off + 1;
    output integer fib3 = off + 2;
    output integer fib4 = off + 3;
    output integer fib5 = off + 5;
    output integer fib6 = off + 8;
    output integer fib7 = off + 13;
    output integer fib8 = off + 21;
    output integer fib9 = off + 34;
endmodule
