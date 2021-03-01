`define TEST(typ, width, is_signed) \
    if (1) begin \
        typ x = -1; \
        localparam typ y = -1; \
        logic [127:0] a = x; \
        logic [127:0] b = y; \
        if ($bits(x) != width) \
            $error(`"typ doesn't have expected size width`"); \
        if ($bits(x) != $bits(y)) \
            $error(`"localparam typ doesn't match size of typ`"); \
        function automatic typ f; \
            input integer x; \
            f = x; \
        endfunction \
        logic [127:0] c = f(-1); \
        always @* begin \
            assert (x == y); \
            assert (a == b); \
            assert (a == c); \
            assert ((a == -1) == is_signed); \
        end \
    end

`define TEST_INTEGER_ATOM(typ, width) \
    `TEST(typ, width, 1) \
    `TEST(typ signed, width, 1) \
    `TEST(typ unsigned, width, 0)

`define TEST_INTEGER_VECTOR(typ) \
    `TEST(typ, 1, 0) \
    `TEST(typ signed, 1, 1) \
    `TEST(typ unsigned, 1, 0) \
    `TEST(typ [1:0], 2, 0) \
    `TEST(typ signed [1:0], 2, 1) \
    `TEST(typ unsigned [1:0], 2, 0)

module top;
    `TEST_INTEGER_ATOM(integer, 32)
    `TEST_INTEGER_ATOM(int, 32)
    `TEST_INTEGER_ATOM(shortint, 16)
    `TEST_INTEGER_ATOM(longint, 64)
    `TEST_INTEGER_ATOM(byte, 8)

    `TEST_INTEGER_VECTOR(reg)
    `TEST_INTEGER_VECTOR(logic)
    `TEST_INTEGER_VECTOR(bit)
endmodule
