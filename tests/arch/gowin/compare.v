module top
(
    input [4:0] x,
    input [4:0] y,

    output lt,
    output le,
    output gt,
    output ge,
    output eq,
    output ne
);

    assign lt = x < y;
    assign le = x <= y;
    assign gt = x > y;
    assign ge = x >= y;
    assign eq = x == y;
    assign ne = x != y;
endmodule
