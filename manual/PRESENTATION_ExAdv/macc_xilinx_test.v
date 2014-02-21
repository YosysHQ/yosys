module test1(a, b, c, d, e, f, y);
    input [19:0] a, b, c;
    input [15:0] d, e, f;
    output [41:0] y;
    assign y = a*b + c*d + e*f;
endmodule

module test2(a, b, c, d, e, f, y);
    input [19:0] a, b, c;
    input [15:0] d, e, f;
    output [41:0] y;
    assign y = a*b + (c*d + e*f);
endmodule
