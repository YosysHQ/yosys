`define INITS \
    assign a = -1; \
    assign b = -2; \
    assign c = -3; \
    assign d = -4; \
    assign a_ext = a; \
    assign b_ext = b; \
    assign c_ext = c; \
    assign d_ext = d;

module gate_a(
    output byte a,
    output byte unsigned b,
    output shortint c,
    output shortint unsigned d,
    output [31:0] a_ext,
    output [31:0] b_ext,
    output [31:0] c_ext,
    output [31:0] d_ext
);
    `INITS
endmodule

module gate_b(
    a, b, c, d,
    a_ext, b_ext, c_ext, d_ext
);
    output byte a;
    output byte unsigned b;
    output shortint c;
    output shortint unsigned d;
    output [31:0] a_ext;
    output [31:0] b_ext;
    output [31:0] c_ext;
    output [31:0] d_ext;
    `INITS
endmodule

module gold(
    output signed [7:0] a,
    output unsigned [7:0] b,
    output signed [15:0] c,
    output unsigned [15:0] d,
    output [31:0] a_ext,
    output [31:0] b_ext,
    output [31:0] c_ext,
    output [31:0] d_ext
);
    `INITS
endmodule
