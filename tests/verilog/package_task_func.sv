package P;
    localparam Y = 2;
    localparam X = Y + 1;
    task t;
        output integer x;
        x = Y;
    endtask
    function automatic integer f;
        input integer i;
        f = i * X;
    endfunction
    function automatic integer g;
        input integer i;
        g = i == 0 ? 1 : Y * g(i - 1);
    endfunction
    localparam Z = g(4);
endpackage

module top;
    integer a;
    initial P::t(a);
    integer b = P::f(3);
    integer c = P::g(3);
    integer d = P::Z;

    assert property (a == 2);
    assert property (b == 9);
    assert property (c == 8);
    assert property (d == 16);
endmodule
