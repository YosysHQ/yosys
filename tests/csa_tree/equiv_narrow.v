// Narrow-width test designs for SAT equivalence (4-bit to keep SAT fast)

module equiv_add3(
    input  [3:0] a, b, c,
    output [3:0] y
);
    assign y = a + b + c;
endmodule

module equiv_add4(
    input  [3:0] a, b, c, d,
    output [3:0] y
);
    assign y = a + b + c + d;
endmodule

module equiv_add5(
    input  [3:0] a, b, c, d, e,
    output [3:0] y
);
    assign y = a + b + c + d + e;
endmodule

module equiv_add8(
    input  [3:0] a, b, c, d, e, f, g, h,
    output [3:0] y
);
    assign y = a + b + c + d + e + f + g + h;
endmodule

module equiv_signed(
    input  signed [3:0] a, b, c, d,
    output signed [5:0] y
);
    assign y = a + b + c + d;
endmodule

module equiv_mixed_w(
    input  [1:0] a,
    input  [3:0] b,
    input  [5:0] c,
    output [5:0] y
);
    assign y = a + b + c;
endmodule

module equiv_repeated(
    input  [3:0] a,
    output [3:0] y
);
    assign y = a + a + a + a;
endmodule

module equiv_1bit_wide(
    input  a, b, c, d,
    output [3:0] y
);
    assign y = a + b + c + d;
endmodule
